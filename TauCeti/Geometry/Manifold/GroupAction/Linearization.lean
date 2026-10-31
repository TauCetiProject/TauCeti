/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.GroupAction.GermKernel
import TauCeti.Analysis.Calculus.InverseFunctionTheorem
import TauCeti.Geometry.Manifold.MFDeriv.Chart

/-!
# Smooth finite-group linearization

A finite group acting by `C^n` maps on a boundaryless Banach manifold admits an equivariant
`C^n` chart at each common fixed point, for `1 ≤ n`. Both the chart and its inverse are `C^n`
on their entire domains. In finite-dimensional real inner product spaces the target can be
chosen to be an invariant ball for an averaged inner product, inside any prescribed
neighbourhood of the fixed point.

This upgrades topological linearization to smooth local models. No faithfulness is required:
the linear representation has exactly the original ineffective germ kernel.

The proof uses `ContRepresentation.bochnerAverage` and the inverse function theorem with a
`C^n` inverse on its whole target (`TauCeti.ContDiffOn.exists_openPartialHomeomorph`).

## References

* S. Bochner, *Compact groups of differentiable transformations*, Ann. of Math. (2) 46 (1945),
  372–381.
* A. Adem, J. Leida and Y. Ruan, *Orbifolds and Stringy Topology*, Chapter 1.
-/

public noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff

namespace TauCeti

variable {𝕜 E H M G : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [CompleteSpace E] [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [Group G] [Finite G] [MulAction G M]
  {n : WithTop ℕ∞} [IsManifold I n M]

/-- **Smooth Bochner linearization.** A finite group acting by `C^n` maps, `1 ≤ n`, has an
invariant chart at a common fixed point in which its action is linear. The chart and its
inverse are `C^n` on their whole domains, and the representation detects the germ kernel. -/
theorem exists_equivariant_contMDiff_chart
    (hsmooth : ∀ g : G, ContMDiff I I n fun z : M => g • z) (hn : 1 ≤ n)
    {x : M} (hx : ∀ g : G, g • x = x) :
    ∃ (σ : ContRepresentation 𝕜 G E) (e : OpenPartialHomeomorph M E),
      x ∈ e.source ∧ e x = 0 ∧
      ContMDiffOn I 𝓘(𝕜, E) n e e.source ∧
      ContMDiffOn 𝓘(𝕜, E) I n e.symm e.target ∧
      (∀ g : G, ∀ z ∈ e.source, g • z ∈ e.source ∧ e (g • z) = σ g (e z)) ∧
      ∀ g : G, σ g = 1 ↔ g ∈ MulAction.germKernel G x := by
  let : Fintype G := Fintype.ofFinite G
  let : ContinuousConstSMul G M := ⟨fun g => (hsmooth g).continuous⟩
  let : Invertible (Fintype.card G : 𝕜) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  let χ := (chartAt H x).transHomeomorph I.toHomeomorph
  have hxχ : x ∈ χ.source := mem_chart_source H x
  have hχ : ⇑χ = extChartAt I x := by ext; simp [χ]
  have hχs : ⇑χ.symm = (extChartAt I x).symm := by ext; simp [χ]
  have hχsmooth : ContMDiffOn I 𝓘(𝕜, E) n χ χ.source := by
    simpa [hχ, χ] using (contMDiffOn_extChartAt (I := I) (n := n) (x := x))
  have hχsymm : ContMDiffOn 𝓘(𝕜, E) I n χ.symm χ.target := by
    simpa [hχs, χ, ModelWithCorners.toHomeomorph, I.range_eq_univ] using
      (contMDiffOn_extChartAt_symm (I := I) (n := n) x)
  have hL (g : G) : HasStrictFDerivAt (χ ∘ (g • ·) ∘ χ.symm)
      (fderiv 𝕜 (χ ∘ (g • ·) ∘ χ.symm) (χ x)) (χ x) := by
    have h := ((hsmooth g x).of_le hn).hasStrictFDerivAt_extChartAt_conj
    rw [hx g] at h
    rwa [hχ, hχs]
  let σ := isotropyRepresentation hxχ hx fun g => (hL g).differentiableAt
  have hσ (g : G) : HasStrictFDerivAt (χ ∘ (g • ·) ∘ χ.symm) (σ g) (χ x) :=
    hasStrictFDerivAt_conj_smul_isotropyRepresentation hxχ hx hL g
  let A := σ.bochnerAverage (fun z => χ z - χ x)
  have hA : HasStrictFDerivAt (A ∘ χ.symm) (ContinuousLinearMap.id 𝕜 E) (χ x) := by
    exact ContRepresentation.hasStrictFDerivAt_bochnerAverage_comp_of_intertwining
      fun g => by
        simpa only [ContinuousLinearMap.comp_id, Function.comp_def] using (hσ g).sub_const (χ x)
  -- All translates must stay in the original chart before averaging its coordinates.
  let U : Set M := ⋂ g : G, (g • ·) ⁻¹' χ.source
  have hU : IsOpen U := isOpen_iInter_of_finite fun g =>
    χ.open_source.preimage (continuous_const_smul g)
  have hxU : x ∈ U := by simp [U, hx, hxχ]
  let V := χ.target ∩ χ.symm ⁻¹' U
  have hV : IsOpen V := χ.isOpen_inter_preimage_symm hU
  have hxV : χ x ∈ V := ⟨χ.map_source hxχ, by simpa [χ.left_inv hxχ] using hxU⟩
  have hAsmooth : ContDiffOn 𝕜 n (A ∘ χ.symm) V := by
    apply ContRepresentation.contDiffOn_bochnerAverage_comp
    intro g
    have hg : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, E) n (χ ∘ (g • ·) ∘ χ.symm) V :=
      hχsmooth.comp
        (((hsmooth g).contMDiffOn (s := Set.univ)).comp (hχsymm.mono inter_subset_left)
          (fun _ _ => mem_univ _))
        (fun z hz => mem_iInter.mp hz.2 g)
    exact hg.contDiffOn.sub contDiffOn_const
  obtain ⟨Θ, hΘ, hxΘ, hΘV, hΘsymm⟩ :=
    TauCeti.ContDiffOn.exists_openPartialHomeomorph hAsmooth hV hxV hn
      (e := ContinuousLinearEquiv.refl 𝕜 E) hA.hasFDerivAt.fderiv.symm
  let e₀ := χ.trans Θ
  have he₀smooth : ContMDiffOn I 𝓘(𝕜, E) n e₀ e₀.source :=
    ((hΘ ▸ hAsmooth.mono hΘV).contMDiffOn).comp
      (hχsmooth.mono inter_subset_left) inter_subset_right
  have he₀symm : ContMDiffOn 𝓘(𝕜, E) I n e₀.symm e₀.target :=
    hχsymm.comp (hΘsymm.contMDiffOn.mono inter_subset_left) inter_subset_right
  -- Intersect the finitely many translates of the inverse-function neighbourhood.
  let W : Set M := ⋂ g : G, (g • ·) ⁻¹' e₀.source
  have hW : IsOpen W := isOpen_iInter_of_finite fun g =>
    e₀.open_source.preimage (continuous_const_smul g)
  let e := e₀.restrOpen W hW
  have hmem {z : M} : z ∈ e.source ↔ ∀ g : G, g • z ∈ e₀.source := by
    simp only [e, OpenPartialHomeomorph.restrOpen_source, W, mem_inter_iff,
      mem_iInter, mem_preimage]
    exact ⟨And.right, fun h => ⟨by simpa using h 1, h⟩⟩
  have hxe : x ∈ e.source := hmem.mpr fun g => by
    rw [hx g]
    exact ⟨hxχ, hxΘ⟩
  have hmaps {z : M} (hz : z ∈ e.source) (g : G) : g • z ∈ e.source := by
    apply hmem.mpr
    intro h
    simpa [mul_smul] using hmem.mp hz (h * g)
  have heA {z : M} (hz : z ∈ e.source) : e z = A z := by
    simp only [e, e₀, OpenPartialHomeomorph.coe_restrOpen, OpenPartialHomeomorph.coe_trans,
      hΘ, Function.comp_apply, χ.left_inv hz.1.1]
  refine ⟨σ, e, hxe, ?_, he₀smooth.mono inter_subset_left,
    he₀symm.mono inter_subset_left, fun g z hz => ⟨hmaps hz g, ?_⟩,
    χ.map_eq_one_iff_mem_germKernel hxχ hx σ hσ⟩
  · rw [heA hxe]
    dsimp only [A]
    rw [ContRepresentation.bochnerAverage_apply_of_forall_smul_eq _ _ hx, sub_self, map_zero]
  · rw [heA (hmaps hz g), heA hz]
    exact σ.bochnerAverage_smul _ g z

end TauCeti

namespace TauCeti

variable {E H M G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [Group G] [Fintype G] [MulAction G M]
  {n : WithTop ℕ∞} [IsManifold I n M]

/-- **Smooth invariant-ball local model.** Inside every neighbourhood of a common fixed point
of a finite `C^n` action there is an equivariant `C^n` chart onto a ball of an averaged inner
product. Its source is invariant and preconnected, and no ineffective isotropy is removed. -/
theorem exists_equivariant_contMDiff_chart_target_eq_sumOfConjugatesInnerSublevel
    (hsmooth : ∀ g : G, ContMDiff I I n fun z : M => g • z) (hn : 1 ≤ n)
    {x : M} (hx : ∀ g : G, g • x = x) {s : Set M} (hs : s ∈ 𝓝 x) :
    ∃ (σ : ContRepresentation ℝ G E) (e : OpenPartialHomeomorph M E) (c : ℝ),
      0 < c ∧ x ∈ e.source ∧ e x = 0 ∧ e.source ⊆ s ∧
      e.target = σ.toRepresentation.sumOfConjugatesInnerSublevel c ∧
      IsPreconnected e.source ∧
      ContMDiffOn I 𝓘(ℝ, E) n e e.source ∧
      ContMDiffOn 𝓘(ℝ, E) I n e.symm e.target ∧
      (∀ g : G, ∀ z ∈ e.source, g • z ∈ e.source ∧ e (g • z) = σ g (e z)) ∧
      ∀ g : G, σ g = 1 ↔ g ∈ MulAction.germKernel G x := by
  obtain ⟨σ, e₀, hxe₀, he₀x, he₀smooth, he₀symm, he₀, hker⟩ :=
    exists_equivariant_contMDiff_chart hsmooth hn hx
  obtain ⟨e, c, hc, hxe, hcoe, hes, het, hconn, he⟩ :=
    e₀.exists_target_eq_sumOfConjugatesInnerSublevel σ.toRepresentation hxe₀ he₀x he₀ hs
  have htarget : e.target ⊆ e₀.target := by
    intro w hw
    rw [← e.right_inv hw, hcoe]
    exact e₀.map_source (hes (e.map_target hw)).1
  have hinv : EqOn e.symm e₀.symm e.target := by
    intro w hw
    calc
      e.symm w = e₀.symm (e₀ (e.symm w)) :=
        (e₀.left_inv (hes (e.map_target hw)).1).symm
      _ = e₀.symm w := by rw [← hcoe, e.right_inv hw]
  refine ⟨σ, e, c, hc, hxe, ?_, fun z hz => (hes hz).2, het, hconn, ?_,
    (he₀symm.mono htarget).congr hinv, he, hker⟩
  · rw [hcoe]
    exact he₀x
  · rw [hcoe]
    exact he₀smooth.mono fun z hz => (hes hz).1

end TauCeti
