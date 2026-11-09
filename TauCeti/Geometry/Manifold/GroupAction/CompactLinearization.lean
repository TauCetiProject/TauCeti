/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.GroupAction.GermKernel
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.RepresentationTheory.Continuous.Basic

import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import TauCeti.Analysis.Calculus.InverseFunctionTheorem
import TauCeti.Analysis.Calculus.ParametricIntegral
import TauCeti.Geometry.Manifold.ContMDiff.PartialDeriv
import TauCeti.RepresentationTheory.Compact.Haar
import TauCeti.Topology.Algebra.ConstMulAction

/-!
# Smooth linearization of compact group actions at fixed points

Let a compact group `G`, itself a manifold without boundary, act on a manifold `M` without
boundary by a jointly `C^n` map `G × M → M`, `1 ≤ n`, and let `x` be a fixed point of the action.
This file proves **Bochner's linearization theorem**: there is a `C^n` chart `e` around `x`, with
`C^n` inverse, `G`-invariant domain and `e x = 0`, in which `G` acts linearly
(`TauCeti.exists_equivariant_contMDiff_chart_of_compactSpace`). The linear action is the isotropy
representation `σ` of `G` at `x`, read in the preferred chart `extChartAt I x`: `σ g` is the
derivative at `x` of `g • ·` in that chart, and `e` has derivative the identity at `x` in that
chart.

Consequently the fixed locus `M^G` is, near each of its points, a linear subspace in a smooth
chart: a point `z` of the domain of `e` is fixed by `G` exactly when `e z` lies in the subspace
`σ.invariants` of vectors fixed by the isotropy representation
(`TauCeti.exists_contMDiff_chart_fixedPoints`). So `M^G` is a union of embedded submanifolds,
whose tangent space at `x` is the space of tangent vectors fixed by the isotropy representation.

The chart is constructed as for a finite group (`TauCeti.exists_equivariant_contMDiff_chart`),
with the sum over the group replaced by an integral against the normalized Haar measure
`TauCeti.haarProb G`. Writing `χ = extChartAt I x`, the average

`A y = ∫ g, σ g (χ (g⁻¹ • y) - χ x) dg`

is `G`-equivariant by left invariance of Haar measure, and has derivative the identity at `x`
because the derivative of `χ (g⁻¹ • ·)` at `x` is `σ g⁻¹`. The inverse function theorem makes it
a chart. Its smoothness is differentiation under the integral sign
(`TauCeti.contDiffOn_integral_smul_of_continuousOn_iteratedFDeriv`): the partial derivatives in
the chart variable of the integrand are jointly continuous in the chart variable and the group
element (`ContMDiffOn.continuousOn_iteratedFDeriv_partial`), since the action is jointly
smooth. Compactness of `G` makes the largest `G`-invariant subset of the domain open
(`TauCeti.isOpen_setOf_forall_smul_mem`).

## Main results

* `ContRepresentation.integral_apply_inv_smul_smul`: the integral average
  `y ↦ ∫ g, σ g (c (g⁻¹ • y)) ∂μ` of a map `c` against a left-invariant measure is equivariant.
* `TauCeti.exists_equivariant_contMDiff_chart_of_compactSpace`: smooth Bochner linearization of
  a compact group action at a fixed point.
* `TauCeti.exists_contMDiff_chart_fixedPoints`: near a fixed point, the fixed locus of a compact
  group action is the preimage of the invariant subspace of the isotropy representation under a
  smooth chart.

## References

* S. Bochner, *Compact groups of differentiable transformations*, Ann. of Math. (2) 46 (1945),
  372–381.
* J. J. Duistermaat and J. A. C. Kolk, *Lie Groups*, Universitext, Springer, 2000, Section 2.2.
* V. Guillemin and S. Sternberg, *Convexity properties of the moment mapping*, Invent. Math. 67
  (1982), 491–513, where the fixed loci of torus actions are the critical submanifolds of
  moment-map components.
-/

public noncomputable section

open Set Filter MeasureTheory Function
open scoped Topology Manifold ContDiff

namespace ContRepresentation

/-- **Equivariance of the integral Bochner average.** For a left-invariant measure `μ` on `G`, a
continuous representation `σ` and any map `c : X → F` from a `G`-space, the average
`y ↦ ∫ g, σ g (c (g⁻¹ • y)) ∂μ` intertwines the action on `X` with `σ`. -/
theorem integral_apply_inv_smul_smul {G X F : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant] [MulAction G X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (σ : ContRepresentation ℝ G F) (c : X → F) (h : G)
    (y : X) : ∫ g, σ g (c (g⁻¹ • h • y)) ∂μ = σ h (∫ g, σ g (c (g⁻¹ • y)) ∂μ) := by
  let L : F ≃L[ℝ] F := ContinuousLinearEquiv.equivOfInverse (σ h) (σ h⁻¹)
    (fun v ↦ by rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def, ← map_mul,
      inv_mul_cancel, map_one]; rfl)
    (fun v ↦ by rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def, ← map_mul,
      mul_inv_cancel, map_one]; rfl)
  calc ∫ g, σ g (c (g⁻¹ • h • y)) ∂μ = ∫ g, σ (h * g) (c ((h * g)⁻¹ • h • y)) ∂μ :=
        (integral_mul_left_eq_self (fun g ↦ σ g (c (g⁻¹ • h • y))) h).symm
    _ = ∫ g, L (σ g (c (g⁻¹ • y))) ∂μ := by
        congr 1
        ext g
        simp [L, mul_inv_rev, mul_smul, map_mul]
    _ = σ h (∫ g, σ g (c (g⁻¹ • y)) ∂μ) := L.integral_comp_comm _

end ContRepresentation

namespace TauCeti

section Linearization

variable {E H M EG HG G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [NormedAddCommGroup EG] [NormedSpace ℝ EG] [TopologicalSpace HG]
  {IG : ModelWithCorners ℝ EG HG} [IG.Boundaryless] [TopologicalSpace G] [ChartedSpace HG G]
  [Group G] [IsTopologicalGroup G] [CompactSpace G] [MulAction G M] {n : ℕ∞}
  [IsManifold I n M] [IsManifold IG n G]

omit [CompleteSpace E] [I.Boundaryless] [IG.Boundaryless] [IsTopologicalGroup G] [CompactSpace G]
  [IsManifold I n M] [IsManifold IG n G] in
/-- In the coordinates of a chart `χ`, the action is a jointly `C^n` map `(w, g) ↦ χ (g • χ.symm w)`
on the open set of pairs for which it is defined. -/
private theorem isOpen_and_contMDiffOn_chart_smul
    (hsmooth : ContMDiff (IG.prod I) I n fun p : G × M ↦ p.1 • p.2)
    {χ : OpenPartialHomeomorph M E} (hχ : ContMDiffOn I 𝓘(ℝ, E) n χ χ.source)
    (hχs : ContMDiffOn 𝓘(ℝ, E) I n χ.symm χ.target) :
    IsOpen {p : E × G | p.1 ∈ χ.target ∧ p.2 • χ.symm p.1 ∈ χ.source} ∧
      ContMDiffOn (𝓘(ℝ, E).prod IG) 𝓘(ℝ, E) n (fun p : E × G ↦ χ (p.2 • χ.symm p.1))
        {p : E × G | p.1 ∈ χ.target ∧ p.2 • χ.symm p.1 ∈ χ.source} := by
  have hj : ContMDiffOn (𝓘(ℝ, E).prod IG) (IG.prod I) n (fun p : E × G ↦ (p.2, χ.symm p.1))
      (χ.target ×ˢ univ) :=
    contMDiffOn_snd.prodMk (hχs.comp contMDiffOn_fst fun p hp ↦ hp.1)
  have hjW : ContMDiffOn (𝓘(ℝ, E).prod IG) (IG.prod I) n (fun p : E × G ↦ (p.2, χ.symm p.1))
      {p : E × G | p.1 ∈ χ.target ∧ p.2 • χ.symm p.1 ∈ χ.source} :=
    hj.mono fun p hp ↦ ⟨hp.1, mem_univ _⟩
  refine ⟨?_, hχ.comp (hsmooth.comp_contMDiffOn hjW) fun p hp ↦ hp.2⟩
  have h := (hsmooth.continuous.comp_continuousOn hj.continuousOn).isOpen_inter_preimage
    (χ.open_target.prod isOpen_univ) χ.open_source
  convert h using 1
  ext p
  simp [and_comm]

omit [CompleteSpace E] [I.Boundaryless] [IsTopologicalGroup G] [CompactSpace G]
  [IsManifold I n M] in
/-- The isotropy representation at a fixed point of a jointly `C¹` action is continuous: in the
coordinates of a chart `χ`, `σ g` is the derivative of `χ (g • χ.symm ·)` at `χ x`, which is
continuous in `g`. -/
private theorem continuous_of_hasStrictFDerivAt_conj_smul
    (hsmooth : ContMDiff (IG.prod I) I n fun p : G × M ↦ p.1 • p.2) (hn : 1 ≤ n)
    {χ : OpenPartialHomeomorph M E} (hχ : ContMDiffOn I 𝓘(ℝ, E) n χ χ.source)
    (hχs : ContMDiffOn 𝓘(ℝ, E) I n χ.symm χ.target) {x : M} (hxχ : x ∈ χ.source)
    (hx : ∀ g : G, g • x = x) {σ : ContRepresentation ℝ G E}
    (hσ : ∀ g : G, HasStrictFDerivAt (χ ∘ (g • ·) ∘ χ.symm) (σ g) (χ x)) : Continuous σ := by
  obtain ⟨hW, hΨ⟩ := isOpen_and_contMDiffOn_chart_smul hsmooth hχ hχs
  have hcont := hΨ.continuousOn_iteratedFDeriv_partial hW (k := 1) (by exact_mod_cast hn)
  refine continuous_iff_continuousAt.mpr fun g ↦ ?_
  have h := (hcont.continuousAt (hW.mem_nhds ⟨χ.map_source hxχ, by
    simpa [χ.left_inv hxχ, hx g]⟩)).comp (x := g)
    (continuous_const.prodMk continuous_id).continuousAt
  refine ((continuousMultilinearCurryFin1 ℝ E E).continuous.continuousAt.comp h).congr
    (Eventually.of_forall fun g ↦ ?_)
  ext v
  simp only [comp_apply, continuousMultilinearCurryFin1_apply, iteratedFDeriv_one_apply]
  rw [← (hσ g).hasFDerivAt.fderiv]
  simp [Function.comp_def]

/-- **Smooth Bochner linearization for compact groups.** Let a compact group `G`, a manifold
without boundary, act on a manifold `M` without boundary by a jointly `C^n` map, `1 ≤ n`, fixing
`x`. Then there is a chart `e` at `x` with `G`-invariant domain, sending `x` to `0`, with `C^n`
inverse, in which `g` acts linearly by `σ g`. Here `σ` is the continuous isotropy representation
of `G` at `x`, read in the chart `extChartAt I x`, and `e` has derivative the identity at `x` in
that chart. -/
theorem exists_equivariant_contMDiff_chart_of_compactSpace
    (hsmooth : ContMDiff (IG.prod I) I n fun p : G × M ↦ p.1 • p.2) (hn : 1 ≤ n) {x : M}
    (hx : ∀ g : G, g • x = x) :
    ∃ (σ : ContRepresentation ℝ G E) (e : OpenPartialHomeomorph M E),
      Continuous σ ∧ x ∈ e.source ∧ e x = 0 ∧
      ContMDiffOn I 𝓘(ℝ, E) n e e.source ∧ ContMDiffOn 𝓘(ℝ, E) I n e.symm e.target ∧
      (∀ g : G, ∀ z ∈ e.source, g • z ∈ e.source ∧ e (g • z) = σ g (e z)) ∧
      (∀ g : G, σ g =
        fderiv ℝ (extChartAt I x ∘ (g • ·) ∘ (extChartAt I x).symm) (extChartAt I x x)) ∧
      HasFDerivAt (e ∘ (extChartAt I x).symm) (ContinuousLinearMap.id ℝ E)
        (extChartAt I x x) := by
  -- Outline: in the coordinates of `χ = extChartAt I x`, average `σ g (χ (g⁻¹ • ·) - χ x)` over
  -- `G` against normalized Haar measure. The average `A'` is `C^n` by differentiation under the
  -- integral sign, has derivative the identity at `χ x`, and is equivariant. The inverse function
  -- theorem makes it a chart `Θ`, and `e` is `χ.trans Θ` restricted to the largest invariant
  -- open subset of its source.
  have : ContinuousSMul G M := ⟨hsmooth.continuous⟩
  have hn' : (1 : WithTop ℕ∞) ≤ n := by exact_mod_cast hn
  have hsmul (g : G) : ContMDiff I I n fun z : M ↦ g • z :=
    hsmooth.comp (contMDiff_const.prodMk contMDiff_id)
  obtain ⟨χ, σ, hxχ, hχ, hχs, hχsource, hχt, hσ⟩ :=
    exists_chart_isotropyRepresentation (𝕜 := ℝ) (fun g ↦ ((hsmul g) x).of_le hn') hx
  have hχsmooth : ContMDiffOn I 𝓘(ℝ, E) n χ χ.source := by
    simpa only [hχ, hχsource, extChartAt_source] using
      (contMDiffOn_extChartAt (I := I) (n := n) (x := x))
  have hχsymm : ContMDiffOn 𝓘(ℝ, E) I n χ.symm χ.target := by
    simpa only [hχs, hχt] using (contMDiffOn_extChartAt_symm (I := I) (n := n) x)
  have hσfd (g : G) : fderiv ℝ (χ ∘ (g • ·) ∘ χ.symm) (χ x) = σ g := (hσ g).hasFDerivAt.fderiv
  -- The action in the coordinates of `χ`, centred at `χ x`, as a jointly smooth map of the
  -- chart variable `w` and the group element `h`.
  let Ψ : E × G → E := fun p ↦ χ (p.2 • χ.symm p.1) - χ x
  let W : Set (E × G) := {p | p.1 ∈ χ.target ∧ p.2 • χ.symm p.1 ∈ χ.source}
  obtain ⟨hW, hΨ₀⟩ := isOpen_and_contMDiffOn_chart_smul hsmooth hχsmooth hχsymm
  have hΨ : ContMDiffOn (𝓘(ℝ, E).prod IG) 𝓘(ℝ, E) n Ψ W :=
    (contDiff_id.sub contDiff_const).contMDiff.comp_contMDiffOn hΨ₀
  have hΨcont (k : ℕ) (hk : (k : ℕ∞) ≤ n) := hΨ.continuousOn_iteratedFDeriv_partial hW
    (k := k) (by exact_mod_cast hk)
  have hxW (g : G) : (χ x, g) ∈ W := ⟨χ.map_source hxχ, by simpa [χ.left_inv hxχ, hx g]⟩
  have hσcont : Continuous σ :=
    continuous_of_hasStrictFDerivAt_conj_smul hsmooth hn hχsmooth hχsymm hxχ hx hσ
  -- The averaged integrand `Φ (w, g) = σ g (Ψ (w, g⁻¹))` on the open set `U` of chart points
  -- whose whole orbit stays in the source of `χ`.
  let Φ : E × G → E := fun p ↦ σ p.2 (Ψ (p.1, p.2⁻¹))
  let U : Set E := {w | ∀ g : G, (w, g) ∈ W}
  have hU : IsOpen U := by
    have hc : IsClosed (Prod.fst '' Wᶜ) := isClosedMap_fst_of_compactSpace _ hW.isClosed_compl
    convert hc.isOpen_compl using 1
    ext w
    simp [U]
  have hxU : χ x ∈ U := hxW
  have hΨU (g : G) : ContDiffOn ℝ n (fun w ↦ Ψ (w, g)) U := by
    rw [← contMDiffOn_iff_contDiffOn]
    exact hΨ.comp (contMDiffOn_id.prodMk contMDiffOn_const) fun w hw ↦ hw g
  have hΦU (g : G) : ContDiffOn ℝ n (fun w ↦ Φ (w, g)) U :=
    (σ g).contDiff.comp_contDiffOn (hΨU g⁻¹)
  have hΦcont (k : ℕ) (hk : (k : ℕ∞) ≤ n) : ContinuousOn
      (fun p : E × G ↦ iteratedFDeriv ℝ k (fun w ↦ Φ (w, p.2)) p.1) (U ×ˢ univ) := by
    have hD : ContinuousOn
        (fun p : E × G ↦ iteratedFDeriv ℝ k (fun w ↦ Ψ (w, p.2⁻¹)) p.1) (U ×ˢ univ) :=
      (hΨcont k hk).comp (continuous_fst.prodMk continuous_snd.inv).continuousOn
        fun p hp ↦ hp.1 p.2⁻¹
    refine (((ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin k ↦ E) E
      E).continuous.comp (hσcont.comp continuous_snd)).continuousOn.clm_apply hD).congr
      fun p hp ↦ ?_
    exact (σ p.2).iteratedFDeriv_comp_left
      ((hΨU p.2⁻¹).contDiffAt (hU.mem_nhds hp.1)) (by exact_mod_cast hk)
  borelize G
  let μ : Measure G := haarProb G
  -- The Bochner average in the coordinates of `χ`, and on `M`.
  let A' : E → E := fun w ↦ ∫ g, Φ (w, g) ∂μ
  let A : M → E := fun y ↦ ∫ g, σ g (χ (g⁻¹ • y) - χ x) ∂μ
  have hA'A {y : M} (hy : y ∈ χ.source) : A' (χ y) = A y := by
    simp [A', A, Φ, Ψ, χ.left_inv hy]
  have hAsmul (h : G) (y : M) : A (h • y) = σ h (A y) :=
    σ.integral_apply_inv_smul_smul μ (fun z ↦ χ z - χ x) h y
  have hA'smooth : ContDiffOn ℝ n A' U := by
    simpa only [one_smul] using contDiffOn_integral_smul_of_continuousOn_iteratedFDeriv
      (g := fun _ ↦ (1 : ℝ)) (integrable_const (1 : ℝ)) hU hΦU hΦcont
  -- At `χ x` the average has derivative the identity, since `σ g ∘ σ g⁻¹ = 1`.
  have hΦ₀ : ContinuousOn Φ (U ×ˢ univ) :=
    ((continuousMultilinearCurryFin0 ℝ E E).continuous.comp_continuousOn
      (hΦcont 0 (by simp))).congr fun p _ ↦ by simp
  have hΦ₁ : ContinuousOn (fun p : E × G ↦ fderiv ℝ (fun w ↦ Φ (w, p.2)) p.1) (U ×ˢ univ) :=
    ((continuousMultilinearCurryFin1 ℝ E E).continuous.comp_continuousOn
      (hΦcont 1 hn)).congr fun p _ ↦ by ext v; simp [iteratedFDeriv_one_apply]
  have hΦfd (g : G) : fderiv ℝ (fun w ↦ Φ (w, g)) (χ x) = ContinuousLinearMap.id ℝ E := by
    have h : HasFDerivAt (fun w ↦ Φ (w, g)) ((σ g).comp (σ g⁻¹)) (χ x) :=
      (σ g).hasFDerivAt.comp (χ x) ((hσ g⁻¹).hasFDerivAt.sub_const (χ x))
    rw [h.fderiv, ← ContinuousLinearMap.mul_def, ← map_mul, mul_inv_cancel, map_one]
    rfl
  have hA'deriv : HasFDerivAt A' (ContinuousLinearMap.id ℝ E) (χ x) := by
    have h := hasFDerivAt_integral_smul_of_continuousOn_fderiv (g := fun _ ↦ (1 : ℝ))
      (integrable_const (1 : ℝ)) (μ := μ) hU hΦ₀
      (fun g ↦ (hΦU g).differentiableOn (zero_lt_one.trans_le hn').ne') hΦ₁ hxU
    simpa only [one_smul, hΦfd, integral_const, probReal_univ] using h
  have hA'x : A' (χ x) = 0 := by
    simp [A', Φ, Ψ, χ.left_inv hxχ, hx]
  -- The inverse function theorem turns the average into a chart.
  obtain ⟨Θ, hΘ, hxΘ, hΘU, hΘsymm⟩ :=
    TauCeti.ContDiffOn.exists_openPartialHomeomorph hA'smooth hU hxU hn'
      (e := ContinuousLinearEquiv.refl ℝ E) hA'deriv.fderiv.symm
  let e₀ := χ.trans Θ
  have he₀ {y : M} (hy : y ∈ e₀.source) : e₀ y = A y := by
    simp only [e₀, OpenPartialHomeomorph.coe_trans, comp_apply, hΘ]
    exact hA'A hy.1
  have he₀smooth : ContMDiffOn I 𝓘(ℝ, E) n e₀ e₀.source :=
    ((hΘ ▸ hA'smooth.mono hΘU).contMDiffOn).comp
      (hχsmooth.mono inter_subset_left) inter_subset_right
  have he₀symm : ContMDiffOn 𝓘(ℝ, E) I n e₀.symm e₀.target :=
    hχsymm.comp (hΘsymm.contMDiffOn.mono inter_subset_left) inter_subset_right
  -- Restrict to the largest invariant open subset of the source.
  let S : Set M := {y | ∀ g : G, g • y ∈ e₀.source}
  have hS : IsOpen S := isOpen_setOf_forall_smul_mem (G := G) e₀.open_source
  let e := e₀.restrOpen S hS
  have hSsource {y : M} (hy : y ∈ S) : y ∈ e₀.source := by simpa using hy 1
  have hesource {y : M} : y ∈ e.source ↔ y ∈ S := by
    simp only [e, OpenPartialHomeomorph.restrOpen_source, mem_inter_iff]
    exact ⟨And.right, fun h ↦ ⟨hSsource h, h⟩⟩
  have hxS : x ∈ S := fun g ↦ by
    rw [hx g]
    exact ⟨hxχ, hxΘ⟩
  refine ⟨σ, e, hσcont, hesource.2 hxS, ?_, ?_, ?_, fun g z hz ↦ ?_, fun g ↦ ?_, ?_⟩
  · change e₀ x = 0
    rw [he₀ (hSsource hxS), ← hA'A hxχ, hA'x]
  · exact he₀smooth.mono (e₀.restrOpen_source S hS ▸ inter_subset_left)
  · exact he₀symm.mono fun w hw ↦ hw.1
  · have hz' := hesource.1 hz
    have hgz : g • z ∈ S := fun h ↦ by rw [smul_smul]; exact hz' (h * g)
    refine ⟨hesource.2 hgz, ?_⟩
    change e₀ (g • z) = σ g (e₀ z)
    rw [he₀ (hSsource hgz), he₀ (hSsource hz'), hAsmul]
  · rw [← hσfd g, hχ, hχs]
  · rw [← hχ, ← hχs]
    refine hA'deriv.congr_of_eventuallyEq ?_
    filter_upwards [χ.open_target.mem_nhds (χ.map_source hxχ),
      (χ.continuousAt_symm (χ.map_source hxχ)).preimage_mem_nhds
        (hS.mem_nhds (by rwa [χ.left_inv hxχ]))] with w hw hwS
    change e₀ (χ.symm w) = A' w
    rw [he₀ (hSsource hwS), ← hA'A (χ.map_target hw), χ.right_inv hw]

/-- **Fixed loci of compact group actions are locally linear.** Under the hypotheses of
`TauCeti.exists_equivariant_contMDiff_chart_of_compactSpace`, there is a `C^n` chart `e` at the
fixed point `x`, with `C^n` inverse, `e x = 0` and derivative the identity at `x` in the chart
`extChartAt I x`, which carries the fixed points of `G` in its domain exactly to the vectors fixed
by the isotropy representation `σ` of `G` at `x`. -/
theorem exists_contMDiff_chart_fixedPoints
    (hsmooth : ContMDiff (IG.prod I) I n fun p : G × M ↦ p.1 • p.2) (hn : 1 ≤ n) {x : M}
    (hx : ∀ g : G, g • x = x) :
    ∃ (σ : ContRepresentation ℝ G E) (e : OpenPartialHomeomorph M E),
      x ∈ e.source ∧ e x = 0 ∧
      ContMDiffOn I 𝓘(ℝ, E) n e e.source ∧ ContMDiffOn 𝓘(ℝ, E) I n e.symm e.target ∧
      (∀ g : G, σ g =
        fderiv ℝ (extChartAt I x ∘ (g • ·) ∘ (extChartAt I x).symm) (extChartAt I x x)) ∧
      HasFDerivAt (e ∘ (extChartAt I x).symm) (ContinuousLinearMap.id ℝ E)
        (extChartAt I x x) ∧
      ∀ z ∈ e.source, (∀ g : G, g • z = z) ↔ e z ∈ σ.invariants := by
  obtain ⟨σ, e, -, hxe, hex, he, hes, hequiv, hσ, hderiv⟩ :=
    exists_equivariant_contMDiff_chart_of_compactSpace hsmooth hn hx
  refine ⟨σ, e, hxe, hex, he, hes, hσ, hderiv, fun z hz ↦ ⟨fun h g ↦ ?_, fun h g ↦ ?_⟩⟩
  · rw [← (hequiv g z hz).2, h g]
  · exact e.injOn (hequiv g z hz).1 hz (by rw [(hequiv g z hz).2, h g])

end Linearization

end TauCeti
