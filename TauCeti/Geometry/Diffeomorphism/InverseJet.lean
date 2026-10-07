/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Evaluation
public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Differential
public import TauCeti.Topology.Homeomorph.Family

/-!
# Continuity of inverse evaluation and first coordinate derivatives

For diffeomorphisms with compact source, inverse evaluation is jointly continuous for the weak
Whitney topology. In fixed source and target charts, the differential of the inverse is the
inverse of the forward differential at the inverse image point. This formula and Mathlib's
`ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse` give joint continuity of the inverse
differential and openness of compact coordinate-differential tests on inverse maps.

The chart differentials are taken within extended chart targets, so the statements also apply
to manifolds with boundary and corners.

The topology convention follows M. Hirsch, *Differential Topology*, GTM 33, Chapter 2, §1.
-/

public section

open Set Filter Topology
open scoped Manifold ContDiff TauCeti.DiffeomorphWeakWhitney TauCeti.ManifoldWeakWhitney

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners 𝕜 F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω}

section Evaluation

variable [CompactSpace M] [T2Space N] [LocallyCompactSpace E]
  [IsManifold I n M] [IsManifold J n N]

/-- Evaluation of inverse diffeomorphisms is jointly continuous in the diffeomorphism and the
target point, for the weak Whitney topology. -/
theorem continuous_diffeomorph_symm_eval :
    Continuous fun p : (M ≃ₘ^n⟮I, J⟯ N) × N ↦ p.1.symm p.2 :=
  continuous_homeomorph_symm_eval (fun f : M ≃ₘ^n⟮I, J⟯ N ↦ f.toHomeomorph)
    ContinuousEval.continuous_eval

/-- The underlying continuous maps of inverse diffeomorphisms depend continuously on the
diffeomorphism. The target here carries the compact-open topology. -/
theorem continuous_diffeomorph_symm_toContinuousMap :
    Continuous fun f : M ≃ₘ^n⟮I, J⟯ N ↦ (f.symm.toHomeomorph : C(N, M)) :=
  ContinuousMap.continuous_of_continuous_uncurry _ continuous_diffeomorph_symm_eval

end Evaluation

section Differential

variable [IsManifold I n M] [IsManifold J n N]

/-- The inverse and forward coordinate differentials compose to the identity, in any pair of
charts containing the point and its image. -/
theorem fderivWithin_diffeomorph_chart_symm_comp (f : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0)
    {x z : M} {y : N} (hz : z ∈ (extChartAt I x).source)
    (hfz : f z ∈ (extChartAt J y).source) :
    (fderivWithin 𝕜 (extChartAt I x ∘ f.symm ∘ (extChartAt J y).symm)
      (extChartAt J y).target (extChartAt J y (f z))).comp
      (fderivWithin 𝕜 (extChartAt J y ∘ f ∘ (extChartAt I x).symm)
        (extChartAt I x).target (extChartAt I x z)) = ContinuousLinearMap.id 𝕜 E := by
  let φ := extChartAt I x
  let ψ := extChartAt J y
  let A : E → F := ψ ∘ f ∘ φ.symm
  let B : F → E := φ ∘ f.symm ∘ ψ.symm
  have hw : φ z ∈ φ.target := φ.map_source hz
  have hA : DifferentiableWithinAt 𝕜 A φ.target (φ z) := by
    simpa only [A, φ, ψ, Diffeomorph.toContMDiffMap, ContMDiffMap.coeFn_mk] using
      (f.toContMDiffMap.contDiffWithinAt_extChartAt (x := x) (y := y) hw
        (by simpa only [Diffeomorph.toContMDiffMap, ContMDiffMap.coeFn_mk, φ,
          (extChartAt I x).left_inv hz] using hfz)).differentiableWithinAt hn
  have hB : DifferentiableWithinAt 𝕜 B ψ.target (ψ (f z)) := by
    simpa only [B, φ, ψ, Diffeomorph.toContMDiffMap, ContMDiffMap.coeFn_mk] using
      (f.symm.toContMDiffMap.contDiffWithinAt_extChartAt (x := y) (y := x) (ψ.map_source hfz)
        (by simpa only [Diffeomorph.toContMDiffMap, ContMDiffMap.coeFn_mk, ψ,
          (extChartAt J y).left_inv hfz, Diffeomorph.symm_apply_apply]
          using hz)).differentiableWithinAt hn
  have hnear : ∀ᶠ w in 𝓝[φ.target] (φ z), f (φ.symm w) ∈ ψ.source :=
    f.continuous.continuousAt.eventually_mem_extChartAt_source hw
      (by simpa only [φ, (extChartAt I x).left_inv hz] using hfz)
  have hAt : Tendsto A (𝓝[φ.target] (φ z)) (𝓝[ψ.target] (A (φ z))) :=
    tendsto_nhdsWithin_iff.mpr ⟨hA.continuousWithinAt,
      hnear.mono fun w hw ↦ ψ.map_source hw⟩
  have hB' : HasFDerivWithinAt B
      (fderivWithin 𝕜 B ψ.target (ψ (f z))) ψ.target (A (φ z)) := by
    simpa only [A, Function.comp_apply, φ.left_inv hz] using hB.hasFDerivWithinAt
  have hcomp := hB'.comp_of_tendsto (φ z) hA.hasFDerivWithinAt hAt
  have hid : B ∘ A =ᶠ[𝓝[φ.target] (φ z)] id := by
    filter_upwards [hnear, self_mem_nhdsWithin] with w hfw hw
    simp only [B, A, Function.comp_apply, ψ.left_inv hfw, Diffeomorph.symm_apply_apply,
      φ.right_inv hw, id_eq]
  have hD := hcomp.fderivWithin ((uniqueDiffOn_extChartAt_target x) _ hw)
  rw [hid.fderivWithin_eq_of_mem hw,
    fderivWithin_id ((uniqueDiffOn_extChartAt_target x) _ hw)] at hD
  exact hD.symm

/-- In fixed charts, the coordinate differential of the inverse is the inverse of the forward
coordinate differential. The derivatives within extended chart targets include boundary points. -/
theorem inverse_fderivWithin_diffeomorph_chart (f : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0)
    {x z : M} {y : N} (hz : z ∈ (extChartAt I x).source)
    (hfz : f z ∈ (extChartAt J y).source) :
    (fderivWithin 𝕜 (extChartAt J y ∘ f ∘ (extChartAt I x).symm)
      (extChartAt I x).target (extChartAt I x z)).inverse =
    fderivWithin 𝕜 (extChartAt I x ∘ f.symm ∘ (extChartAt J y).symm)
      (extChartAt J y).target (extChartAt J y (f z)) := by
  have hss : f.symm.symm = f := Diffeomorph.ext fun _ ↦ rfl
  apply ContinuousLinearMap.inverse_eq
  · simpa only [hss, Diffeomorph.symm_apply_apply] using
      fderivWithin_diffeomorph_chart_symm_comp f.symm hn hfz
        (by simpa only [Diffeomorph.symm_apply_apply] using hz)
  · exact fderivWithin_diffeomorph_chart_symm_comp f hn hz hfz

/-- Coordinate differentials of a diffeomorphism are invertible, including at boundary points. -/
theorem isInvertible_fderivWithin_diffeomorph_chart (f : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0)
    {x z : M} {y : N} (hz : z ∈ (extChartAt I x).source)
    (hfz : f z ∈ (extChartAt J y).source) :
    (fderivWithin 𝕜 (extChartAt J y ∘ f ∘ (extChartAt I x).symm)
      (extChartAt I x).target (extChartAt I x z)).IsInvertible := by
  have hss : f.symm.symm = f := Diffeomorph.ext fun _ ↦ rfl
  apply ContinuousLinearMap.IsInvertible.of_inverse
  · simpa only [hss, Diffeomorph.symm_apply_apply] using
      fderivWithin_diffeomorph_chart_symm_comp f.symm hn hfz
        (by simpa only [Diffeomorph.symm_apply_apply] using hz)
  · exact fderivWithin_diffeomorph_chart_symm_comp f hn hz hfz

end Differential

section Continuity

variable [CompactSpace M] [T2Space N] [LocallyCompactSpace E]
  [IsManifold I n M] [IsManifold J n N]

/-- The first coordinate differential of the inverse varies continuously with the
diffeomorphism and the point of the target chart. -/
theorem tendsto_fderivWithin_diffeomorph_symm_extChartAt
    {f₀ : M ≃ₘ^n⟮I, J⟯ N} {x : M} {y : N} {w₀ : F} (hn : 1 ≤ n)
    (hw₀ : w₀ ∈ (extChartAt J y).target)
    (hf₀ : f₀.symm ((extChartAt J y).symm w₀) ∈ (extChartAt I x).source) :
    Tendsto (fun p : (M ≃ₘ^n⟮I, J⟯ N) × F ↦
      fderivWithin 𝕜 (extChartAt I x ∘ p.1.symm ∘ (extChartAt J y).symm)
        (extChartAt J y).target p.2)
      (𝓝 f₀ ×ˢ 𝓝[(extChartAt J y).target] w₀)
      (𝓝 (fderivWithin 𝕜 (extChartAt I x ∘ f₀.symm ∘ (extChartAt J y).symm)
        (extChartAt J y).target w₀)) := by
  let : CompleteSpace E := IsLeftUniformAddGroup.completeSpace_of_weaklyLocallyCompactSpace E
  let φ := extChartAt I x
  let ψ := extChartAt J y
  let z₀ := f₀.symm (ψ.symm w₀)
  let l := 𝓝 f₀ ×ˢ 𝓝[ψ.target] w₀
  let v := fun p : (M ≃ₘ^n⟮I, J⟯ N) × F ↦ p.1.symm (ψ.symm p.2)
  have hn' : n ≠ 0 := by
    rintro rfl
    simp at hn
  have hz₀ : f₀ z₀ ∈ ψ.source := by
    simpa only [z₀, Diffeomorph.apply_symm_apply] using ψ.map_target hw₀
  -- Track the inverse image point and keep it inside the chosen source chart.
  have hpt : Tendsto (fun p : (M ≃ₘ^n⟮I, J⟯ N) × F ↦ (p.1, ψ.symm p.2)) l
      (𝓝 (f₀, ψ.symm w₀)) := by
    rw [nhds_prod_eq]
    exact (tendsto_fst : Tendsto Prod.fst l (𝓝 f₀)).prodMk
      ((continuousOn_extChartAt_symm y w₀ hw₀).tendsto.comp tendsto_snd)
  have hv : Tendsto v l (𝓝 z₀) :=
    ((continuous_diffeomorph_symm_eval (I := I) (J := J) (n := n)).tendsto
      (f₀, ψ.symm w₀)).comp hpt
  have hsrc : ∀ᶠ p in l, v p ∈ φ.source :=
    hv.eventually ((isOpen_extChartAt_source x).mem_nhds hf₀)
  have hφ : Tendsto (fun p ↦ φ (v p)) l (𝓝[φ.target] (φ z₀)) :=
    tendsto_nhdsWithin_iff.mpr ⟨(continuousOn_extChartAt x z₀ hf₀).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨hv, hsrc⟩), hsrc.mono fun _ hp ↦ φ.map_source hp⟩
  -- Evaluate the forward differential at the moving inverse image, then invert it.
  have hq : Tendsto (fun p : (M ≃ₘ^n⟮I, J⟯ N) × F ↦ (p.1.toContMDiffMap, φ (v p))) l
      (𝓝 f₀.toContMDiffMap ×ˢ 𝓝[φ.target] (φ z₀)) :=
    (Diffeomorph.continuous_toContMDiffMap.continuousAt.tendsto.comp
      (tendsto_fst : Tendsto Prod.fst l (𝓝 f₀))).prodMk hφ
  have hz₀' : z₀ ∈ φ.source := hf₀
  have hvis : f₀.toContMDiffMap (φ.symm (φ z₀)) ∈ ψ.source := by
    simpa only [Diffeomorph.toContMDiffMap, ContMDiffMap.coeFn_mk, φ.left_inv hz₀'] using hz₀
  have hD : Tendsto (fun p : (M ≃ₘ^n⟮I, J⟯ N) × F ↦
      fderivWithin 𝕜 (ψ ∘ p.1 ∘ φ.symm) φ.target (φ (v p))) l
      (𝓝 (fderivWithin 𝕜 (ψ ∘ f₀ ∘ φ.symm) φ.target (φ z₀))) := by
    simpa only [Function.comp_def, Diffeomorph.toContMDiffMap, ContMDiffMap.coeFn_mk] using
      (tendsto_fderivWithin_extChartAt hn (φ.map_source hf₀) hvis).comp hq
  have hinv := isInvertible_fderivWithin_diffeomorph_chart f₀ hn' hf₀ hz₀
  have hlim := (hinv.contDiffAt_map_inverse (n := 1)).continuousAt.tendsto.comp hD
  rw [inverse_fderivWithin_diffeomorph_chart f₀ hn' hf₀ hz₀] at hlim
  simp only [Diffeomorph.apply_symm_apply, (extChartAt J y).right_inv hw₀] at hlim
  -- The inverse formula identifies these operators with the desired chart differentials.
  apply hlim.congr'
  filter_upwards [hsrc, tendsto_snd.eventually self_mem_nhdsWithin] with p hp hw
  have hz : p.1 (v p) ∈ ψ.source := by
    simpa only [v, Diffeomorph.apply_symm_apply] using ψ.map_target hw
  simpa only [Function.comp_apply, v, φ, ψ, Diffeomorph.apply_symm_apply,
    (extChartAt J y).right_inv hw] using
    inverse_fderivWithin_diffeomorph_chart p.1 hn' hp hz

/-- A compact coordinate-differential test on inverse maps is open in the weak Whitney
topology. The test also requires all inverse images to lie in the chosen source chart. -/
theorem isOpen_diffeomorph_symm_fderivWithin_test (hn : 1 ≤ n) (x : M) (y : N)
    {K : Set (extChartAt J y).target} (hK : IsCompact K) {V : Set (F →L[𝕜] E)}
    (hV : IsOpen V) :
    IsOpen {f : M ≃ₘ^n⟮I, J⟯ N | ∀ w ∈ K,
      f.symm ((extChartAt J y).symm w) ∈ (extChartAt I x).source ∧
        fderivWithin 𝕜 (extChartAt I x ∘ f.symm ∘ (extChartAt J y).symm)
          (extChartAt J y).target w ∈ V} := by
  refine isOpen_iff_mem_nhds.mpr fun f₀ hf₀ ↦ ?_
  refine hK.eventually_forall_of_forall_eventually fun w hw ↦ ?_
  have he : Continuous (fun p : (M ≃ₘ^n⟮I, J⟯ N) × (extChartAt J y).target ↦
      p.1.symm ((extChartAt J y).symm p.2)) :=
    continuous_diffeomorph_symm_eval.comp (continuous_fst.prodMk
      ((continuousOn_iff_continuous_domRestrict.mp
        (continuousOn_extChartAt_symm (I := J) y)).comp continuous_snd))
  have hsrc : ∀ᶠ p : (M ≃ₘ^n⟮I, J⟯ N) × (extChartAt J y).target in 𝓝 (f₀, w),
      p.1.symm ((extChartAt J y).symm p.2) ∈ (extChartAt I x).source :=
    he.continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source x).mem_nhds (hf₀ w hw).1)
  have hD := (tendsto_fderivWithin_diffeomorph_symm_extChartAt hn w.2 (hf₀ w hw).1).eventually
    (hV.mem_nhds (hf₀ w hw).2)
  rw [nhds_prod_eq] at hsrc ⊢
  exact hsrc.and ((tendsto_id.prodMap (map_nhds_subtype_val w).le).eventually hD)

end Continuity

end TauCeti
