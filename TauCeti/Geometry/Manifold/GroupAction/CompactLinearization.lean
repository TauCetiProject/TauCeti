/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.GroupAction.TangentRepresentation

import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import TauCeti.Analysis.Calculus.IteratedFDeriv.Prod
import TauCeti.Analysis.Calculus.ParametricIntegral
import TauCeti.Geometry.Manifold.Algebra.SMul
import TauCeti.Geometry.Manifold.ContMDiff.PartialDeriv
import TauCeti.Geometry.Manifold.ContMDiff.InverseFunctionTheorem
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.RepresentationTheory.Compact.Haar
import TauCeti.RepresentationTheory.Continuous.Average
import TauCeti.Topology.Algebra.ConstMulAction
import TauCeti.Topology.OpenPartialHomeomorph.MulAction

/-!
# Smooth linearization of compact group actions at fixed points

Let a compact group `G`, itself a manifold without boundary, act on a manifold `M` without
boundary by a jointly `C^n` map `G × M → M` (`ContMDiffSMul`), `1 ≤ n`, and let `x` be a fixed
point of the action. This file proves **Bochner's linearization theorem**: there is a `C^n` chart
`e` around `x`, with `C^n` inverse, `G`-invariant domain, `e x = 0` and derivative the identity at
`x`, in which `G` acts linearly (`TauCeti.exists_equivariant_contMDiff_chart_of_compactSpace`).
The linear action is the isotropy representation `σ g = mfderiv I I (g • ·) x` of `G` on
`T_x M = E`, which is `TauCeti.tangentRepresentation` since the stabilizer of `x` is all of `G`.

Consequently the fixed locus `M^G` is, near each of its points, a linear subspace in a smooth
chart: in an equivariant chart `e` as above, a point `z` of the domain of `e` is fixed by `G`
exactly when `e z` lies in the subspace of vectors fixed by the tangent representation at `x`
(`TauCeti.exists_contMDiff_chart_fixedPoints`). This is the local model for a submanifold
structure on `M^G` with tangent space the invariant vectors at `x`; that structure is not
constructed here.

The chart is constructed as for a finite group (`TauCeti.exists_equivariant_contMDiff_chart`),
with the sum over the group replaced by an integral against the normalized Haar measure
`TauCeti.haarProb G`. Writing `χ = extChartAt I x`, the average

`A y = ∫ g, σ g (χ (g⁻¹ • y) - χ x) dg`

is `G`-equivariant by left invariance of Haar measure
(`ContRepresentation.integral_apply_inv_smul_smul`), and has derivative the identity at `x`
because the derivative of `χ (g⁻¹ • ·)` at `x` is `σ g⁻¹`. The inverse function theorem makes it
a chart. Its smoothness is differentiation under the integral sign
(`TauCeti.contDiffOn_integral_smul_of_continuousOn_iteratedFDeriv`): the partial derivatives in
the chart variable of the integrand are jointly continuous in the chart variable and the group
element (`ContMDiffOn.continuousOn_iteratedFDeriv_partial`), since the action is jointly
smooth. Compactness of `G` makes the largest `G`-invariant subset of the domain open
(`TauCeti.isOpen_setOf_forall_smul_mem`).

## Main results

* `TauCeti.exists_equivariant_contMDiff_chart_of_compactSpace`: smooth Bochner linearization of
  a compact group action at a fixed point.
* `TauCeti.exists_contMDiff_chart_fixedPoints`: near a fixed point, the fixed locus of a compact
  group action is the preimage of the invariant subspace of the tangent representation under a
  smooth chart in which the action is the tangent representation.

## References

* S. Bochner, *Compact groups of differentiable transformations*, Ann. of Math. (2) 46 (1945),
  372–381.
* J. J. Duistermaat and J. A. C. Kolk, *Lie Groups*, Universitext, Springer, 2000, Section 2.2.
* V. Guillemin and S. Sternberg, *Convexity properties of the moment mapping*, Invent. Math. 67
  (1982), 491–513, where the fixed loci of torus actions are the critical submanifolds of
  moment-map components.
-/

public noncomputable section

open Set Filter MeasureTheory Function MulAction
open scoped Topology Manifold ContDiff

namespace TauCeti

section Linearization

variable {E H M EG HG G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [NormedAddCommGroup EG] [NormedSpace ℝ EG] [TopologicalSpace HG]
  {IG : ModelWithCorners ℝ EG HG} [IG.Boundaryless] [TopologicalSpace G] [ChartedSpace HG G]
  [Group G] [IsTopologicalGroup G] [CompactSpace G] [MulAction G M] {n : ℕ∞}
  [IsManifold I n M] [IsManifold IG n G]

omit [I.Boundaryless] [IsManifold I n M] in
variable (IG) in
/-- **The Bochner average in a chart.** Let `χ` be a chart at a fixed point `x` in which `g • ·`
has derivative `σ g` at `x`, for a continuous representation `σ`. On the open set `U` of chart
points whose whole orbit stays in the source of `χ`, the average
`w ↦ ∫ g, σ g (χ (g⁻¹ • χ.symm w) - χ x)` is `C^n`, with derivative the identity at `χ x`. -/
private theorem contDiffOn_and_hasFDerivAt_chart_average [MeasurableSpace G] [BorelSpace G]
    [ContMDiffSMul IG I n G M] (hn : 1 ≤ n) {χ : OpenPartialHomeomorph M E}
    (hχ : ContMDiffOn I 𝓘(ℝ, E) n χ χ.source) (hχs : ContMDiffOn 𝓘(ℝ, E) I n χ.symm χ.target)
    {x : M} (hxχ : x ∈ χ.source) (hx : ∀ g : G, g • x = x) {σ : ContRepresentation ℝ G E}
    (hσcont : Continuous σ) (hσ : ∀ g : G, HasFDerivAt (χ ∘ (g • ·) ∘ χ.symm) (σ g) (χ x)) :
    IsOpen (χ.target ∩ χ.symm ⁻¹' {y | ∀ g : G, g • y ∈ χ.source}) ∧
      χ x ∈ χ.target ∩ χ.symm ⁻¹' {y | ∀ g : G, g • y ∈ χ.source} ∧
      ContDiffOn ℝ n (fun w ↦ ∫ g, σ g (χ (g⁻¹ • χ.symm w) - χ x) ∂haarProb G)
        (χ.target ∩ χ.symm ⁻¹' {y | ∀ g : G, g • y ∈ χ.source}) ∧
      HasFDerivAt (fun w ↦ ∫ g, σ g (χ (g⁻¹ • χ.symm w) - χ x) ∂haarProb G)
        (ContinuousLinearMap.id ℝ E) (χ x) := by
  have : ContinuousSMul G M :=
    ⟨(ContMDiffSMul.contMDiff_smul (I := IG) (I' := I) (n := n) (G := G) (M := M)).continuous⟩
  have hn' : (1 : WithTop ℕ∞) ≤ n := by exact_mod_cast hn
  -- The action in the coordinates of `χ`, centred at `χ x`, as a jointly smooth map of the
  -- chart variable `w` and the group element `h`.
  let Ψ : E × G → E := fun p ↦ χ (p.2 • χ.symm p.1) - χ x
  let W : Set (E × G) := {p | p.1 ∈ χ.target ∧ p.2 • χ.symm p.1 ∈ χ.source}
  have hW : IsOpen W := χ.isOpen_setOf_mem_target_smul_symm_mem_source
  have hΨ₀ := ContMDiffSMul.contMDiffOn_comp_smul_symm (I := IG) (I' := I) (G := G) hχ hχs
  have hΨ : ContMDiffOn (𝓘(ℝ, E).prod IG) 𝓘(ℝ, E) n Ψ W :=
    (contDiff_id.sub contDiff_const).contMDiff.comp_contMDiffOn hΨ₀
  -- The averaged integrand `Φ (w, g) = σ g (Ψ (w, g⁻¹))` on the open set `U` of chart points
  -- whose whole orbit stays in the source of `χ`.
  let Φ : E × G → E := fun p ↦ σ p.2 (Ψ (p.1, p.2⁻¹))
  let U : Set E := χ.target ∩ χ.symm ⁻¹' {y | ∀ g : G, g • y ∈ χ.source}
  have hU : IsOpen U :=
    χ.isOpen_inter_preimage_symm (isOpen_setOf_forall_smul_mem (G := G) χ.open_source)
  have hUW {w : E} (hw : w ∈ U) (g : G) : (w, g) ∈ W := ⟨hw.1, hw.2 g⟩
  have hxU : χ x ∈ U := ⟨χ.map_source hxχ, by simpa [χ.left_inv hxχ, hx] using hxχ⟩
  have hΨU (g : G) : ContDiffOn ℝ n (fun w ↦ Ψ (w, g)) U := by
    rw [← contMDiffOn_iff_contDiffOn]
    exact hΨ.comp (contMDiffOn_id.prodMk contMDiffOn_const) fun w hw ↦ hUW hw g
  have hΦU (g : G) : ContDiffOn ℝ n (fun w ↦ Φ (w, g)) U :=
    (σ g).contDiff.comp_contDiffOn (hΨU g⁻¹)
  have hΦcont (k : ℕ) (hk : (k : ℕ∞) ≤ n) : ContinuousOn
      (fun p : E × G ↦ iteratedFDeriv ℝ k (fun w ↦ Φ (w, p.2)) p.1) (U ×ˢ univ) :=
    continuousOn_iteratedFDeriv_partial_clm_apply (F := fun p ↦ Ψ (p.1, p.2⁻¹))
      (L := fun g ↦ σ g) (hσcont.comp continuous_snd).continuousOn
      (fun p hp ↦ ((hΨU p.2⁻¹).contDiffAt (hU.mem_nhds hp.1)).of_le (by exact_mod_cast hk))
      ((hΨ.continuousOn_iteratedFDeriv_partial hW (by exact_mod_cast hk)).comp
        (continuous_fst.prodMk continuous_snd.inv).continuousOn fun p hp ↦ hUW hp.1 p.2⁻¹)
  refine ⟨hU, hxU, ?_, ?_⟩
  · simpa only [one_smul] using contDiffOn_integral_smul_of_continuousOn_iteratedFDeriv
      (g := fun _ ↦ (1 : ℝ)) (integrable_const (1 : ℝ)) hU hΦU hΦcont
  -- At `χ x` the average has derivative the identity, since `σ g ∘ σ g⁻¹ = 1`.
  have hΦfd (g : G) : fderiv ℝ (fun w ↦ Φ (w, g)) (χ x) = ContinuousLinearMap.id ℝ E := by
    have h : HasFDerivAt (fun w ↦ Φ (w, g)) ((σ g).comp (σ g⁻¹)) (χ x) :=
      (σ g).hasFDerivAt.comp (χ x) ((hσ g⁻¹).sub_const (χ x))
    rw [h.fderiv, ContRepresentation.comp_inv_self]
  have h := hasFDerivAt_integral_smul_of_continuousOn_fderiv (g := fun _ ↦ (1 : ℝ))
    (integrable_const (1 : ℝ)) (μ := haarProb G) hU
    (continuousOn_iteratedFDeriv_zero_partial_iff.1 (hΦcont 0 (by simp)))
    (fun g ↦ (hΦU g).differentiableOn (zero_lt_one.trans_le hn').ne')
    (continuousOn_iteratedFDeriv_zero_partial_iff.1
      (continuousOn_iteratedFDeriv_fderiv_partial (hΦcont 1 hn))) hxU
  simpa only [one_smul, hΦfd, integral_const, probReal_univ] using h

variable (IG) in
/-- **Smooth Bochner linearization for compact groups.** Let a compact group `G`, a manifold
without boundary, act on a manifold `M` without boundary by a jointly `C^n` map, `1 ≤ n`, fixing
`x`. Then there is a chart `e` at `x` with `G`-invariant domain, sending `x` to `0`, with `C^n`
inverse and derivative the identity at `x`, in which `g` acts linearly by `σ g`. Here `σ` is the
continuous isotropy representation `σ g = mfderiv I I (g • ·) x` of `G` on `T_x M = E`, that is,
`TauCeti.tangentRepresentation` of the stabilizer `G` of `x`. -/
theorem exists_equivariant_contMDiff_chart_of_compactSpace [ContMDiffSMul IG I n G M]
    (hn : 1 ≤ n) {x : M} (hx : ∀ g : G, g • x = x) :
    ∃ (σ : ContRepresentation ℝ G E) (e : OpenPartialHomeomorph M E),
      Continuous σ ∧ x ∈ e.source ∧ e x = 0 ∧
      ContMDiffOn I 𝓘(ℝ, E) n e e.source ∧ ContMDiffOn 𝓘(ℝ, E) I n e.symm e.target ∧
      (∀ g : G, ∀ z ∈ e.source, g • z ∈ e.source ∧ e (g • z) = σ g (e z)) ∧
      (∀ g : G, σ g = mfderiv I I (g • ·) x) ∧
      HasMFDerivAt I 𝓘(ℝ, E) e x (ContinuousLinearMap.id ℝ E) := by
  -- Outline: in the coordinates of `χ = extChartAt I x`, average `σ g (χ (g⁻¹ • ·) - χ x)` over
  -- `G` against normalized Haar measure. The average `A'` is `C^n` by differentiation under the
  -- integral sign, has derivative the identity at `χ x`, and is equivariant. The inverse function
  -- theorem makes it a chart `Θ`, and `e` is `χ.trans Θ` restricted to the largest invariant
  -- open subset of its source.
  have hn' : (1 : WithTop ℕ∞) ≤ n := by exact_mod_cast hn
  have hsmul (g : G) : ContMDiff I I n fun z : M ↦ g • z :=
    ContMDiffSMul.contMDiff_const_smul (I := IG) g
  have : ContinuousSMul G M :=
    ⟨(ContMDiffSMul.contMDiff_smul (I := IG) (I' := I) (n := n) (G := G) (M := M)).continuous⟩
  obtain ⟨χ, σ, hxχ, hχ, hχs, hχsource, hχt, hσ⟩ :=
    exists_chart_isotropyRepresentation (𝕜 := ℝ) (fun g ↦ ((hsmul g) x).of_le hn') hx
  have hχsmooth : ContMDiffOn I 𝓘(ℝ, E) n χ χ.source := by
    simpa only [hχ, hχsource, extChartAt_source] using
      (contMDiffOn_extChartAt (I := I) (n := n) (x := x))
  have hχsymm : ContMDiffOn 𝓘(ℝ, E) I n χ.symm χ.target := by
    simpa only [hχs, hχt] using (contMDiffOn_extChartAt_symm (I := I) (n := n) x)
  -- `σ` is the tangent representation at `x`, hence continuous.
  have hd : ∀ g ∈ stabilizer G x, MDifferentiableAt I I (fun y : M ↦ g • y) x :=
    fun g _ ↦ ((hsmul g) x).mdifferentiableAt (zero_lt_one.trans_le hn').ne'
  have hσmf (g : G) : σ g = mfderiv I I (g • ·) x := by
    rw [(hd g (hx g)).mfderiv_eq_fderiv_extChartAt_conj (hx g), ← hχ, ← hχs]
    exact (hσ g).hasFDerivAt.fderiv.symm
  have hσcont : Continuous σ := by
    have : IsManifold I 1 M := .of_le hn'
    have : IsManifold IG 1 G := .of_le hn'
    have : ContMDiffSMul IG I 1 G M := .of_le hn'
    exact ((continuous_tangentRepresentation IG hd).comp
      (continuous_id.subtype_mk fun g ↦ hx g)).congr fun g ↦
      (tangentRepresentation_apply hd ⟨g, hx g⟩).trans (hσmf g).symm
  borelize G
  obtain ⟨hU, hxU, hA'smooth, hA'deriv⟩ := contDiffOn_and_hasFDerivAt_chart_average IG hn
    hχsmooth hχsymm hxχ hx hσcont fun g ↦ (hσ g).hasFDerivAt
  let μ : Measure G := haarProb G
  -- The Bochner average in the coordinates of `χ`, and on `M`.
  let A' : E → E := fun w ↦ ∫ g, σ g (χ (g⁻¹ • χ.symm w) - χ x) ∂μ
  let A : M → E := fun y ↦ ∫ g, σ g (χ (g⁻¹ • y) - χ x) ∂μ
  have hA'A {y : M} (hy : y ∈ χ.source) : A' (χ y) = A y := by
    simp [A', A, χ.left_inv hy]
  have hAsmul (h : G) (y : M) : A (h • y) = σ h (A y) :=
    σ.integral_apply_inv_smul_smul μ (fun z ↦ χ z - χ x) h y
  have hA'x : A' (χ x) = 0 := by
    simp [A', χ.left_inv hxχ, hx]
  -- The inverse function theorem turns the average into a chart.
  obtain ⟨Θ, hΘ, hxΘ, -, he₀smooth, he₀symm⟩ :=
    exists_contMDiffOn_trans_of_hasFDerivAt hχsmooth hχsymm hA'smooth hU hxU hn' hA'deriv
  let e₀ := χ.trans Θ
  have he₀ {y : M} (hy : y ∈ e₀.source) : e₀ y = A y := by
    simp only [e₀, OpenPartialHomeomorph.coe_trans, comp_apply, hΘ]
    exact hA'A hy.1
  -- Restrict to the largest invariant open subset of the source.
  let S : Set M := {y | ∀ g : G, g • y ∈ e₀.source}
  have hS : IsOpen S := isOpen_setOf_forall_smul_mem (G := G) e₀.open_source
  let e := e₀.restrOpen S hS
  have hee₀ : ⇑e = e₀ := e₀.coe_restrOpen hS
  have hSsource {y : M} (hy : y ∈ S) : y ∈ e₀.source := by simpa using hy 1
  have hesource {y : M} : y ∈ e.source ↔ y ∈ S := by
    simp only [e, OpenPartialHomeomorph.restrOpen_source, mem_inter_iff]
    exact ⟨And.right, fun h ↦ ⟨hSsource h, h⟩⟩
  have hetarget : e.target ⊆ e₀.target := by
    simp only [e, OpenPartialHomeomorph.restrOpen_toPartialEquiv, PartialEquiv.restr_target]
    exact inter_subset_left
  have hxS : x ∈ S := fun g ↦ by
    rw [hx g]
    exact ⟨hxχ, hxΘ⟩
  refine ⟨σ, e, hσcont, hesource.2 hxS, ?_, ?_, ?_, fun g z hz ↦ ?_, hσmf, ?_⟩
  · rw [hee₀, he₀ (hSsource hxS), ← hA'A hxχ, hA'x]
  · rw [hee₀]
    exact he₀smooth.mono fun y hy ↦ hSsource (hesource.1 hy)
  · rw [e₀.coe_restrOpen_symm hS]
    exact he₀symm.mono hetarget
  · have hz' := hesource.1 hz
    have hgz : g • z ∈ S := fun h ↦ by rw [smul_smul]; exact hz' (h * g)
    refine ⟨hesource.2 hgz, ?_⟩
    rw [hee₀, he₀ (hSsource hgz), he₀ (hSsource hz'), hAsmul]
  · refine ⟨e.continuousAt (hesource.2 hxS), ?_⟩
    rw [I.range_eq_univ, hasFDerivWithinAt_univ, writtenInExtChartAt, extChartAt_model_space_eq_id,
      PartialEquiv.refl_coe, id_comp, ← hχ, ← hχs]
    refine hA'deriv.congr_of_eventuallyEq ?_
    filter_upwards [χ.open_target.mem_nhds (χ.map_source hxχ),
      (χ.continuousAt_symm (χ.map_source hxχ)).preimage_mem_nhds
        (hS.mem_nhds (by rwa [χ.left_inv hxχ]))] with w hw hwS
    rw [comp_apply, hee₀, he₀ (hSsource hwS), ← hA'A (χ.map_target hw), χ.right_inv hw]

variable (IG) in
/-- **Fixed loci of compact group actions are locally linear.** Under the hypotheses of
`TauCeti.exists_equivariant_contMDiff_chart_of_compactSpace`, there is a `C^n` chart `e` at the
fixed point `x`, with `C^n` inverse, `G`-invariant domain, `e x = 0` and derivative the identity
at `x`, in which `g` acts by the tangent representation `TauCeti.tangentRepresentation` of the
stabilizer `G` of `x`. The same chart carries the fixed points of `G` in its domain exactly to the
tangent vectors at `x` fixed by this representation. -/
theorem exists_contMDiff_chart_fixedPoints [ContMDiffSMul IG I n G M] (hn : 1 ≤ n) {x : M}
    (hx : ∀ g : G, g • x = x)
    (hd : ∀ g ∈ stabilizer G x, MDifferentiableAt I I (fun y : M ↦ g • y) x) :
    ∃ e : OpenPartialHomeomorph M E,
      x ∈ e.source ∧ e x = 0 ∧
      ContMDiffOn I 𝓘(ℝ, E) n e e.source ∧ ContMDiffOn 𝓘(ℝ, E) I n e.symm e.target ∧
      HasMFDerivAt I 𝓘(ℝ, E) e x (ContinuousLinearMap.id ℝ E) ∧
      (∀ g : G, ∀ z ∈ e.source,
        g • z ∈ e.source ∧ e (g • z) = tangentRepresentation hd ⟨g, hx g⟩ (e z)) ∧
      ∀ z ∈ e.source,
        (∀ g : G, g • z = z) ↔ e z ∈ (tangentRepresentation hd).toRepresentation.invariants := by
  obtain ⟨σ, e, -, hxe, hex, he, hes, hequiv, hσ, hderiv⟩ :=
    exists_equivariant_contMDiff_chart_of_compactSpace (I := I) IG hn hx
  have hσd (g : stabilizer G x) (v : E) : tangentRepresentation hd g v = σ g v :=
    DFunLike.congr_fun ((tangentRepresentation_apply hd g).trans (hσ g).symm) v
  refine ⟨e, hxe, hex, he, hes, hderiv,
    fun g z hz ↦ ⟨(hequiv g z hz).1, (hequiv g z hz).2.trans (hσd ⟨g, hx g⟩ (e z)).symm⟩,
    fun z hz ↦ ?_⟩
  have hinv : e z ∈ (tangentRepresentation hd).toRepresentation.invariants ↔
      ∀ g : G, σ g (e z) = e z := by
    refine (Representation.mem_invariants (tangentRepresentation hd).toRepresentation
      (e z : TangentSpace I x)).trans
      ⟨fun h g ↦ (hσd ⟨g, hx g⟩ (e z)).symm.trans (h ⟨g, hx g⟩),
        fun h g ↦ (hσd g (e z)).trans (h g)⟩
  rw [hinv]
  exact ⟨fun h g ↦ by rw [← (hequiv g z hz).2, h g],
    fun h g ↦ e.injOn (hequiv g z hz).1 hz (by rw [(hequiv g z hz).2, h g])⟩

end Linearization

end TauCeti
