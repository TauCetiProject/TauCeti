/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Submersion.Basic
import TauCeti.Geometry.Manifold.ContMDiff.Atlas
import TauCeti.Geometry.Manifold.IsManifold.InteriorChart

/-!
# Composition of submersions

Structural operations on `Manifold.IsSubmersion` for iterated submersion fibre products:
chart alignment (`IsSubmersionAtOfComplement.exists_domChart_of_codChart`) and composition
(`IsSubmersion.comp`).

## References
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Thms. 4.12, 4.26.
* S. Lang, *Fundamentals of Differential Geometry*, Springer GTM 191 (1999), Chapter II, §2.
-/

public section

noncomputable section

open Function Set Filter
open OpenPartialHomeomorph (transHomeomorph_source transHomeomorph_target trans_source trans_target
  prod_source prod_target refl_source refl_target symm_source transHomeomorph_apply prod_symm
  refl_symm refl_apply extend_target extend_source extend_coe extendTrans_source extendTrans_target
  extendTrans_apply extendTrans_symm_apply)
open scoped Manifold Topology ContDiff

namespace Manifold

section Composition

variable {𝕜 E E' E'' F₁ F₂ H H' H'' M N P : Type*} [NontriviallyNormedField 𝕜] {n : ℕ∞ω}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H'']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' H'} {K : ModelWithCorners 𝕜 E'' H''}
  [I.Boundaryless] [J.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I n M]
  [TopologicalSpace N] [ChartedSpace H' N] [TopologicalSpace P] [ChartedSpace H'' P]
  {f : M → N} {g : N → P} {x : M}

/-- **Aligning a submersion normal form over a prescribed base chart.** Given a point `x` where
`f` is a submersion with complement `F₁` and any maximal-atlas chart `ψ` at `f x`, returns a
maximal-atlas chart `φ` at `x` with `φ.source ⊆ f ⁻¹' ψ.source` in which `f` reads as
`w ↦ (hf.equiv w).1` into `ψ.extend J` (retaining the same linear splitting `hf.equiv`). -/
theorem IsSubmersionAtOfComplement.exists_domChart_of_codChart
    (hf : IsSubmersionAtOfComplement F₁ I J n f x) {ψ : OpenPartialHomeomorph N H'}
    (hfx : f x ∈ ψ.source) (hψ : ψ ∈ IsManifold.maximalAtlas J n N) :
    ∃ φ : OpenPartialHomeomorph M H,
      x ∈ φ.source ∧ φ ∈ IsManifold.maximalAtlas I n M ∧ φ.source ⊆ f ⁻¹' ψ.source ∧
      ∀ w ∈ (φ.extend I).target,
        (hf.equiv w).1 ∈ (ψ.extend J).target ∧
        f ((φ.extend I).symm w) = (ψ.extend J).symm (hf.equiv w).1 ∧
        ψ.extend J (f ((φ.extend I).symm w)) = (hf.equiv w).1 := by
  -- Transport `d₁` to `E' × F₁` via `hf.equiv`, apply the codomain transition `τ = Ψ₁⁻¹ ≫ Φ₂`
  -- on the base factor (`τ × id`), pull back by `hf.equiv⁻¹`, and compose with `I.interiorChart⁻¹`
  -- to obtain `φ = (Φ₁ ≫ (τ × id)) ≫ L⁻¹ ≫ I⁻¹`.
  let d₁ := hf.domChart; let c₁ := hf.codChart
  let Φ₁ := d₁.extendTrans I hf.equiv.toHomeomorph
  let Ψ₁ := c₁.extendTrans J (Homeomorph.refl E')
  let Φ₂ := ψ.extendTrans J (Homeomorph.refl E')
  let τ := Ψ₁.symm.trans Φ₂
  let τF := τ.prod (OpenPartialHomeomorph.refl F₁)
  let Θ := (Φ₁.trans τF).transHomeomorph hf.equiv.symm.toHomeomorph
  let φ := Θ.trans I.interiorChart.symm
  have hΦ₁ := d₁.contMDiffOn_extendTrans hf.domChart_mem_maximalAtlas
    (Ψ := hf.equiv.toHomeomorph) hf.equiv.contDiff
  have hΦ₁s := d₁.contMDiffOn_extendTrans_symm hf.domChart_mem_maximalAtlas
    (Ψ := hf.equiv.toHomeomorph) hf.equiv.symm.contDiff
  have hτ : ContMDiffOn 𝓘(𝕜, E') 𝓘(𝕜, E') n τ τ.source :=
    (ψ.contMDiffOn_extendTrans hψ contDiff_id).comp
      ((c₁.contMDiffOn_extendTrans_symm hf.codChart_mem_maximalAtlas contDiff_id).mono
        inter_subset_left) fun _ hz ↦ hz.2
  have hτs : ContMDiffOn 𝓘(𝕜, E') 𝓘(𝕜, E') n τ.symm τ.target :=
    (c₁.contMDiffOn_extendTrans hf.codChart_mem_maximalAtlas contDiff_id).comp
      ((ψ.contMDiffOn_extendTrans_symm hψ contDiff_id).mono inter_subset_left)
      fun _ hz ↦ hz.2
  have hτF : ContMDiffOn 𝓘(𝕜, E' × F₁) 𝓘(𝕜, E' × F₁) n τF τF.source := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact hτ.prodMap (contMDiffOn_id (I := 𝓘(𝕜, F₁)) (M := F₁))
  have hτFs : ContMDiffOn 𝓘(𝕜, E' × F₁) 𝓘(𝕜, E' × F₁) n τF.symm τF.target := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact hτs.prodMap (contMDiffOn_id (I := 𝓘(𝕜, F₁)) (M := F₁))
  have hΘ : ContMDiffOn I 𝓘(𝕜, E) n Θ Θ.source :=
    hf.equiv.symm.contDiff.contMDiff.comp_contMDiffOn <|
      hτF.comp (hΦ₁.mono inter_subset_left) fun _ hz ↦ hz.2
  have hΘs : ContMDiffOn 𝓘(𝕜, E) I n Θ.symm Θ.target :=
    (hΦ₁s.comp (hτFs.mono inter_subset_left) fun _ hz ↦ hz.2).comp
      hf.equiv.contDiff.contMDiff.contMDiffOn fun _ hw ↦ hw
  have hφ := Θ.trans_interiorChart_symm_mem_maximalAtlas hΘ hΘs
  have hprojx : (Φ₁ x).1 = Ψ₁ (f x) := by
    simpa [Φ₁, Ψ₁, d₁, c₁, extend_coe] using (hf.codChart_extend_apply hf.mem_domChart_source).symm
  have hxφ : x ∈ φ.source := by
    simp only [φ, Θ, τF, τ, transHomeomorph_source, trans_source, prod_source, refl_source,
      symm_source, ModelWithCorners.interiorChart_target, I.range_eq_univ, interior_univ,
      mem_inter_iff, mem_preimage, mem_prod, mem_univ, and_true]
    have hxΦ₁ : x ∈ Φ₁.source := by simpa [Φ₁] using hf.mem_domChart_source
    have hfxΨ₁ : f x ∈ Ψ₁.source := by simpa [Ψ₁] using hf.mem_codChart_source
    rw [hprojx]
    refine ⟨hxΦ₁, Ψ₁.map_source hfxΨ₁, ?_⟩
    rw [Ψ₁.left_inv hfxΨ₁]
    simpa [Φ₂] using hfx
  -- Membership in `(φ.extend I).target` unfolds directly to `Θ.target` (landing in `τ.target`
  -- and `(d₁.extend I).target`), while `(φ.extend I).symm` factors through `d₁.extend I` via `τ⁻¹`.
  have hΘ_target : ∀ {w}, w ∈ (φ.extend I).target →
      ((hf.equiv w).1 ∈ Φ₂.target ∧ Φ₂.symm (hf.equiv w).1 ∈ Ψ₁.source) ∧
      hf.equiv.symm (τ.symm (hf.equiv w).1, (hf.equiv w).2) ∈ (d₁.extend I).target := by
    intro w hw
    have hwΘ : w ∈ Θ.target := by
      rwa [OpenPartialHomeomorph.extend_trans_interiorChart_symm_target] at hw
    simp only [Θ, τF, Φ₁, ContinuousLinearEquiv.toHomeomorph_symm, Homeomorph.symm_symm,
      transHomeomorph_target, trans_target, prod_target, refl_target, prod_symm, refl_symm,
      OpenPartialHomeomorph.prod_apply, refl_apply, extendTrans_target,
      ContinuousLinearEquiv.coe_toHomeomorph, mem_inter_iff, mem_preimage, mem_prod, mem_univ,
      and_true] at hwΘ
    refine ⟨by simpa [τ] using hwΘ.1, ?_⟩
    rw [extend_target, I.range_eq_univ, inter_univ]
    exact hwΘ.2
  have hφ_symm (w : E) : (φ.extend I).symm w =
      (d₁.extend I).symm (hf.equiv.symm (τ.symm (hf.equiv w).1, (hf.equiv w).2)) := by
    dsimp only [φ]
    rw [OpenPartialHomeomorph.extend_trans_interiorChart_symm_symm]
    simp [Θ, τF, Φ₁]
  have hmain : ∀ w ∈ (φ.extend I).target,
      (hf.equiv w).1 ∈ (ψ.extend J).target ∧
      f ((φ.extend I).symm w) = (ψ.extend J).symm (hf.equiv w).1 ∧
      ψ.extend J (f ((φ.extend I).symm w)) = (hf.equiv w).1 := fun w hw ↦ by
    obtain ⟨hu'τ, hzΦ₁⟩ := hΘ_target hw
    set u' : E' := (hf.equiv w).1
    set z : E := hf.equiv.symm (τ.symm u', (hf.equiv w).2)
    have hf_eq : c₁.extend J (f ((d₁.extend I).symm z)) = τ.symm u' := by
      simpa [d₁, c₁, z] using hf.writtenInCharts hzΦ₁
    have hfz_mem : f ((d₁.extend I).symm z) ∈ (c₁.extend J).source := by
      rw [extend_source]
      exact hf.source_subset_preimage_source <|
        by rw [← d₁.extend_source (I := I)]; exact (d₁.extend I).map_target hzΦ₁
    have hf_val : f ((φ.extend I).symm w) = (ψ.extend J).symm u' := by
      rw [hφ_symm, ← (c₁.extend J).left_inv hfz_mem, hf_eq]
      exact (by simp [Ψ₁] : (c₁.extend J).symm (τ.symm u') = Ψ₁.symm (τ.symm u')).trans
        ((Ψ₁.left_inv hu'τ.2).trans (by simp [Φ₂]))
    have hu'ψ : u' ∈ (ψ.extend J).target := by
      simpa [Φ₂, extend_target, J.range_eq_univ] using hu'τ.1
    exact ⟨hu'ψ, hf_val, by rw [hf_val]; exact (ψ.extend J).right_inv hu'ψ⟩
  refine ⟨φ, hxφ, hφ, fun y hy ↦ ?_, hmain⟩
  have hy' : y ∈ (φ.extend I).source := by rwa [φ.extend_source]
  obtain ⟨hu', hfy, -⟩ := hmain (φ.extend I y) ((φ.extend I).map_source hy')
  rw [mem_preimage, ← (φ.extend I).left_inv hy', hfy, ← ψ.extend_source (I := J)]
  exact (ψ.extend J).map_target hu'

/-- **Composition of submersions at a point, keeping track of complements.** -/
theorem IsSubmersionAtOfComplement.comp (hg : IsSubmersionAtOfComplement F₂ J K n g (f x))
    (hf : IsSubmersionAtOfComplement F₁ I J n f x) :
    IsSubmersionAtOfComplement (F₁ × F₂) I K n (g ∘ f) x := by
  obtain ⟨φ, hxφ, hφ, -, hmain⟩ :=
    hf.exists_domChart_of_codChart hg.mem_domChart_source hg.domChart_mem_maximalAtlas
  let L : E ≃L[𝕜] E'' × (F₁ × F₂) :=
    hf.equiv.trans <| (hg.equiv.prodCongr (ContinuousLinearEquiv.refl 𝕜 F₁)).trans <|
      (ContinuousLinearEquiv.prodAssoc 𝕜 E'' F₂ F₁).trans <|
        (ContinuousLinearEquiv.refl 𝕜 E'').prodCongr (ContinuousLinearEquiv.prodComm 𝕜 F₂ F₁)
  refine .mk_of_continuousAt (hg.contMDiffAt.continuousAt.comp hf.contMDiffAt.continuousAt)
    L φ hg.codChart hxφ hg.mem_codChart_source hφ hg.codChart_mem_maximalAtlas fun w hw ↦ ?_
  obtain ⟨hu', hfw, -⟩ := hmain w hw; dsimp only [comp_apply]; rw [hfw]
  exact (hg.writtenInCharts hu').trans (by simp [L])

/-- **Composition of submersions at a point.** The composition `g ∘ f` of a submersion `f` at `x`
and a submersion `g` at `f x` is a submersion at `x`. -/
theorem IsSubmersionAt.comp (hg : IsSubmersionAt J K n g (f x)) (hf : IsSubmersionAt I J n f x) :
    IsSubmersionAt I K n (g ∘ f) x :=
  (hg.isSubmersionAtOfComplement_complement.comp
    hf.isSubmersionAtOfComplement_complement).isSubmersionAt

/-- **Composition of submersions with complements.** If `f` is a submersion with complement `F₁`
and `g` is a submersion with complement `F₂`, then `g ∘ f` is a submersion with complement
`F₁ × F₂`. -/
theorem IsSubmersionOfComplement.comp (hg : IsSubmersionOfComplement F₂ J K n g)
    (hf : IsSubmersionOfComplement F₁ I J n f) :
    IsSubmersionOfComplement (F₁ × F₂) I K n (g ∘ f) :=
  isSubmersionOfComplement_iff.mpr fun x ↦ (hg.isSubmersionAt (f x)).comp (hf.isSubmersionAt x)

/-- **Composition of submersions.** -/
theorem IsSubmersion.comp (hg : IsSubmersion J K n g) (hf : IsSubmersion I J n f) :
    IsSubmersion I K n (g ∘ f) :=
  (hg.isSubmersionOfComplement_complement.comp hf.isSubmersionOfComplement_complement).isSubmersion

end Composition

end Manifold
