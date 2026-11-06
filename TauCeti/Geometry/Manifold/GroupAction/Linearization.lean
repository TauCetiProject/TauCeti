/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.GroupAction.GermKernel
import TauCeti.Analysis.Calculus.InverseFunctionTheorem
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic

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
  -- Choose manifold coordinates and the derivative representation once for both linearizations.
  obtain ⟨χ, σ, hxχ, hχ, hχs, hχsource, hχt, hσ⟩ :=
    exists_chart_isotropyRepresentation (fun g => (hsmooth g x).of_le hn) hx
  have hχsmooth : ContMDiffOn I 𝓘(𝕜, E) n χ χ.source := by
    simpa only [hχ, hχsource, extChartAt_source] using
      (contMDiffOn_extChartAt (I := I) (n := n) (x := x))
  have hχsymm : ContMDiffOn 𝓘(𝕜, E) I n χ.symm χ.target := by
    simpa only [hχs, hχt] using (contMDiffOn_extChartAt_symm (I := I) (n := n) x)
  -- Average on the invariant part of the original chart, where every summand is smooth.
  let A := σ.bochnerAverage (fun z => χ z - χ x)
  have hA : HasStrictFDerivAt (A ∘ χ.symm) (ContinuousLinearMap.id 𝕜 E) (χ x) := by
    exact ContRepresentation.hasStrictFDerivAt_bochnerAverage_comp_of_intertwining
      fun g => by
        simpa only [ContinuousLinearMap.comp_id, Function.comp_def] using (hσ g).sub_const (χ x)
  let U := (χ.restrInvariant G).source
  have hxU : x ∈ U := χ.mem_restrInvariant_source_of_forall_smul_eq hx hxχ
  let V := χ.target ∩ χ.symm ⁻¹' U
  have hV : IsOpen V := χ.isOpen_inter_preimage_symm (χ.restrInvariant G).open_source
  have hxV : χ x ∈ V := ⟨χ.map_source hxχ, by simpa [χ.left_inv hxχ] using hxU⟩
  have hAsmooth : ContDiffOn 𝕜 n (A ∘ χ.symm) V := by
    apply ContRepresentation.contDiffOn_bochnerAverage_comp
    intro g
    have hg : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, E) n (χ ∘ (g • ·) ∘ χ.symm) V :=
      hχsmooth.comp
        (((hsmooth g).contMDiffOn (s := Set.univ)).comp (hχsymm.mono inter_subset_left)
          (fun _ _ => mem_univ _))
        (fun z hz => χ.mem_restrInvariant_source_iff.mp hz.2 g)
    exact hg.contDiffOn.sub contDiffOn_const
  -- The smooth inverse function theorem supplies smoothness on the entire target.
  obtain ⟨Θ, hΘ, hxΘ, hΘV, hΘsymm⟩ :=
    TauCeti.ContDiffOn.exists_openPartialHomeomorph hAsmooth hV hxV hn
      (e := ContinuousLinearEquiv.refl 𝕜 E) hA.hasFDerivAt.fderiv.symm
  let e₀ := χ.trans Θ
  have he₀smooth : ContMDiffOn I 𝓘(𝕜, E) n e₀ e₀.source :=
    ((hΘ ▸ hAsmooth.mono hΘV).contMDiffOn).comp
      (hχsmooth.mono inter_subset_left) inter_subset_right
  have he₀symm : ContMDiffOn 𝓘(𝕜, E) I n e₀.symm e₀.target :=
    hχsymm.comp (hΘsymm.contMDiffOn.mono inter_subset_left) inter_subset_right
  -- Use the common Bochner restriction to retain equivariance without losing smoothness.
  let e := e₀.restrInvariant G
  have hΘeq : EqOn Θ (A ∘ χ.symm) Θ.source := fun z _ => congrFun hΘ z
  have hxe : x ∈ e.source :=
    e₀.mem_restrInvariant_source_of_forall_smul_eq hx ⟨hxχ, hxΘ⟩
  refine ⟨σ, e, hxe, ?_, ?_, ?_, fun g z hz =>
      ⟨e₀.smul_mem_restrInvariant_source hz g,
        OpenPartialHomeomorph.bochnerChart_smul hΘeq hz g⟩,
    χ.map_eq_one_iff_mem_germKernel hxχ hx σ hσ⟩
  · rw [OpenPartialHomeomorph.bochnerChart_apply hΘeq hxe,
      ContRepresentation.bochnerAverage_apply_of_forall_smul_eq _ _ hx, sub_self, map_zero]
  · simpa only [e, OpenPartialHomeomorph.coe_restrInvariant] using
      he₀smooth.mono e₀.restrInvariant_source_subset
  · simpa only [e, OpenPartialHomeomorph.coe_restrInvariant_symm] using
      he₀symm.mono e₀.restrInvariant_target_subset

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
