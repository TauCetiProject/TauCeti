/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Submersion.Basic
public import TauCeti.Geometry.Manifold.Submersion.LocalDiffeomorph
import all Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Composition, local sections, and local-diffeomorphism instances of submersions

This file completes the structural operations on `Manifold.IsSubmersion` needed to build and
manipulate iterated submersion fibre products:

* **Second projections and global local sections.** Complementing `Manifold.isSubmersion_fst`, the
  second projection of a product of manifolds is a submersion with the first model space as
  complement (`Manifold.isSubmersionOfComplement_snd`, `Manifold.isSubmersion_snd`). On a
  boundaryless source manifold, any submersion admits a `C^n` local section through every point of
  its source (`Manifold.IsSubmersion.exists_contMDiffOn_section`), and a surjective submersion
  admits a `C^n` local section around every point of its base
  (`Manifold.IsSubmersion.exists_contMDiffOn_section_of_surjective`), with no separation,
  countability, or finite-dimensionality assumptions.
* **Chart alignment and composition of submersions.** When the source and target models have no
  boundary, a submersion's domain chart can be adjusted to project along `hf.equiv` into any
  prescribed maximal-atlas chart on the base
  (`Manifold.IsSubmersionAtOfComplement.exists_domChart_of_codChart`).
  Consequently, when the source and intermediate models have no boundary, the composite `g ∘ f` of
  submersions with complements `F₁` and `F₂` is a submersion with complement `F₁ × F₂`
  (`Manifold.IsSubmersionAtOfComplement.comp`, `Manifold.IsSubmersionAt.comp`,
  `Manifold.IsSubmersionOfComplement.comp`, `Manifold.IsSubmersion.comp`), with no completeness,
  finite-dimensionality, or `1 ≤ n` assumptions.
* **Local diffeomorphisms and diffeomorphisms as submersions.** Any `C^n` local diffeomorphism
  (`n ≠ 0`) between boundaryless manifolds, even with distinct models, is a submersion with
  complement `PUnit` (`IsLocalDiffeomorphAt.isSubmersionAt`, `IsLocalDiffeomorph.isSubmersion`,
  `Diffeomorph.isSubmersion`), using the invertible differential to align the model vector spaces.
* **Transversality.** Because the differential of a submersion (`n ≠ 0`) is surjective, a submersion
  is automatically transverse on either side to every map into the same target
  (`Manifold.IsSubmersion.transverse_left`, `Manifold.IsSubmersion.transverse_right`).

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Theorem 4.12 (rank theorem for submersions) and Theorem 4.26 (local sections of submersions).
* S. Lang, *Fundamentals of Differential Geometry*, Springer GTM 191 (1999), Chapter II, §2
  (submersions and transversal maps).
-/

public section

noncomputable section

open Function Set Filter
open scoped Manifold Topology ContDiff

namespace Manifold

section SndAndSection

variable {𝕜 E E' F H G M N : Type*} [NontriviallyNormedField 𝕜] {n : ℕ∞ω}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' G}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N] {f : M → N}

/-- The second projection of a product of manifolds is a submersion, with the first model space as
complement. Neither factor needs to be nonempty. -/
theorem isSubmersionOfComplement_snd [IsManifold I n M] [IsManifold J n N] :
    IsSubmersionOfComplement E (I.prod J) J n (@Prod.snd M N) := by
  refine isSubmersionOfComplement_iff.mpr fun p ↦ ?_
  refine .mk_of_continuousAt continuous_snd.continuousAt
    (ContinuousLinearEquiv.prodComm 𝕜 E E') (chartAt (ModelProd H G) p) (chartAt G p.2)
    (mem_chart_source _ p) (mem_chart_source _ p.2) (IsManifold.chart_mem_maximalAtlas p)
    (IsManifold.chart_mem_maximalAtlas p.2) ?_
  intro y hy
  rw [← extChartAt, ← extChartAt] at *
  rw [extChartAt_prod] at hy ⊢
  exact (extChartAt J p.2).right_inv hy.2

/-- The second projection of a product of manifolds is a submersion. -/
theorem isSubmersion_snd [IsManifold I n M] [IsManifold J n N] :
    IsSubmersion (I.prod J) J n (@Prod.snd M N) :=
  isSubmersionOfComplement_snd.isSubmersion

/-- **Local sections of a submersion with fixed complement.** If `f : M → N` is a `C^n` submersion
with complement `F` and the model of `M` has no boundary, then through every `x : M` there is an
open neighbourhood `U` of `f x` and a `C^n` map `s : N → M` on `U` with `s (f x) = x` and
`f (s y) = y` for all `y ∈ U`. -/
theorem IsSubmersionOfComplement.exists_contMDiffOn_section [I.Boundaryless]
    (h : IsSubmersionOfComplement F I J n f) (x : M) :
    ∃ U : Set N, IsOpen U ∧ f x ∈ U ∧ ∃ s : N → M, s (f x) = x ∧ ContMDiffOn J I n s U ∧
      ∀ y ∈ U, f (s y) = y :=
  (h.isSubmersionAt x).exists_contMDiffOn_section

/-- **Local sections of a submersion through every source point.** If `f : M → N` is a `C^n`
submersion and the model of `M` has no boundary, then through every `x : M` there is an open
neighbourhood `U` of `f x` and a `C^n` local section `s` of `f` on `U` with `s (f x) = x`. No
separation, countability, or finite-dimensionality assumption is needed. -/
theorem IsSubmersion.exists_contMDiffOn_section [I.Boundaryless]
    (h : IsSubmersion I J n f) (x : M) :
    ∃ U : Set N, IsOpen U ∧ f x ∈ U ∧ ∃ s : N → M, s (f x) = x ∧ ContMDiffOn J I n s U ∧
      ∀ y ∈ U, f (s y) = y :=
  (h.isSubmersionAt x).exists_contMDiffOn_section

/-- **Local sections of a surjective submersion around every base point.** If `f : M → N` is a
surjective `C^n` submersion with boundaryless source model, every `y : N` has an open neighbourhood
`U` supporting a `C^n` local section `s` of `f`. -/
theorem IsSubmersion.exists_contMDiffOn_section_of_surjective [I.Boundaryless]
    (h : IsSubmersion I J n f) (hsurj : Surjective f) (y : N) :
    ∃ U : Set N, IsOpen U ∧ y ∈ U ∧ ∃ s : N → M, ContMDiffOn J I n s U ∧ ∀ z ∈ U, f (s z) = z := by
  obtain ⟨x, rfl⟩ := hsurj y
  obtain ⟨U, hU, hxU, s, -, hs, hfs⟩ := h.exists_contMDiffOn_section x
  exact ⟨U, hU, hxU, s, hs, hfs⟩

end SndAndSection

section ChartExtendHelpers

variable {𝕜 E H M : Type*} [NontriviallyNormedField 𝕜] {n : ℕ∞ω}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M]

private theorem contMDiffOn_transHomeomorph_toHomeomorph {e : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I n M) :
    ContMDiffOn I 𝓘(𝕜, E) n (e.transHomeomorph I.toHomeomorph)
      (e.transHomeomorph I.toHomeomorph).source := by
  have hcoe : ⇑(e.transHomeomorph I.toHomeomorph) = ⇑I ∘ ⇑e := by
    ext z; exact I.toHomeomorph_apply (e z)
  rw [hcoe, OpenPartialHomeomorph.transHomeomorph_source]
  simpa [OpenPartialHomeomorph.extend_coe] using e.contMDiffOn_extend he

private theorem contMDiffOn_transHomeomorph_toHomeomorph_symm {e : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I n M) :
    ContMDiffOn 𝓘(𝕜, E) I n (e.transHomeomorph I.toHomeomorph).symm
      (e.transHomeomorph I.toHomeomorph).target := by
  have hcoe : ⇑(e.transHomeomorph I.toHomeomorph).symm = ⇑e.symm ∘ ⇑I.symm := by
    ext v; exact congrArg e.symm (I.toHomeomorph_symm_apply v)
  have htarget : (e.transHomeomorph I.toHomeomorph).target = ⇑I '' e.target := by
    rw [OpenPartialHomeomorph.transHomeomorph_target, ← Homeomorph.image_eq_preimage_symm]
    ext v; simp [I.toHomeomorph_apply]
  rw [hcoe, htarget]
  simpa [OpenPartialHomeomorph.extend_coe_symm, OpenPartialHomeomorph.extend_target'] using
    contMDiffOn_extend_symm he

end ChartExtendHelpers

section Composition

variable {𝕜 E E' E'' F₁ F₂ H H' H'' M N P : Type*} [NontriviallyNormedField 𝕜] {n : ℕ∞ω}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H'']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' H'} {K : ModelWithCorners 𝕜 E'' H''}
  [I.Boundaryless] [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I n M]
  [TopologicalSpace N] [ChartedSpace H' N]
  [TopologicalSpace P] [ChartedSpace H'' P]
  {f : M → N} {g : N → P} {x : M}

/-- **Aligning a submersion normal form over a prescribed base chart.** If `f : M → N` is a `C^n`
submersion at `x` with complement `F₁` between manifolds with boundaryless models, then for any
maximal-atlas chart `ψ` of `N` around `f x` there is a maximal-atlas chart `φ` of `M` around `x`
whose source maps into `ψ.source` and in which `f` acts as `(hf.equiv ·).1` followed by
`(ψ.extend J).symm`. This lets a finite family of submersions over the same base point share a
single base chart. -/
theorem IsSubmersionAtOfComplement.exists_domChart_of_codChart
    (hf : IsSubmersionAtOfComplement F₁ I J n f x) {ψ : OpenPartialHomeomorph N H'}
    (hfx : f x ∈ ψ.source) (hψ : ψ ∈ IsManifold.maximalAtlas J n N) :
    ∃ φ : OpenPartialHomeomorph M H,
      x ∈ φ.source ∧ φ ∈ IsManifold.maximalAtlas I n M ∧ φ.source ⊆ f ⁻¹' ψ.source ∧
      ∀ w ∈ (φ.extend I).target,
        (hf.equiv w).1 ∈ (ψ.extend J).target ∧
        f ((φ.extend I).symm w) = (ψ.extend J).symm (hf.equiv w).1 ∧
        ψ.extend J (f ((φ.extend I).symm w)) = (hf.equiv w).1 := by
  -- Read the domain and base charts directly in `E` and `E'` via the boundaryless models.
  let Φ₁ : OpenPartialHomeomorph M E := hf.domChart.transHomeomorph I.toHomeomorph
  let Ψ₁ : OpenPartialHomeomorph N E' := hf.codChart.transHomeomorph J.toHomeomorph
  let Φ₂ : OpenPartialHomeomorph N E' := ψ.transHomeomorph J.toHomeomorph
  -- Transition from `hf.codChart` to `ψ` on `E'`, acting as the identity on `F₁`.
  let τ : OpenPartialHomeomorph E' E' := Ψ₁.symm.trans Φ₂
  let τF : OpenPartialHomeomorph (E' × F₁) (E' × F₁) := τ.prod (OpenPartialHomeomorph.refl F₁)
  let Θ : OpenPartialHomeomorph M E :=
    ((Φ₁.transHomeomorph hf.equiv.toHomeomorph).trans τF).transHomeomorph hf.equiv.symm.toHomeomorph
  let φ : OpenPartialHomeomorph M H := Θ.transHomeomorph I.toHomeomorph.symm
  have hIsymm : ContMDiff 𝓘(𝕜, E) I n I.symm :=
    contMDiffOn_univ.1 (I.range_eq_univ ▸ I.contMDiffOn_symm)
  have hΦ₁ := contMDiffOn_transHomeomorph_toHomeomorph hf.domChart_mem_maximalAtlas
  have hΦ₁symm := contMDiffOn_transHomeomorph_toHomeomorph_symm hf.domChart_mem_maximalAtlas
  have hΨ₁ := contMDiffOn_transHomeomorph_toHomeomorph hf.codChart_mem_maximalAtlas
  have hΨ₁symm := contMDiffOn_transHomeomorph_toHomeomorph_symm hf.codChart_mem_maximalAtlas
  have hΦ₂ := contMDiffOn_transHomeomorph_toHomeomorph hψ
  have hΦ₂symm := contMDiffOn_transHomeomorph_toHomeomorph_symm hψ
  have hτ : ContMDiffOn 𝓘(𝕜, E') 𝓘(𝕜, E') n τ τ.source :=
    hΦ₂.comp (hΨ₁symm.mono inter_subset_left) fun _ hz ↦ hz.2
  have hτsymm : ContMDiffOn 𝓘(𝕜, E') 𝓘(𝕜, E') n τ.symm τ.target :=
    hΨ₁.comp (hΦ₂symm.mono inter_subset_left) fun _ hz ↦ hz.2
  have hfst : ContMDiff 𝓘(𝕜, E' × F₁) 𝓘(𝕜, E') n (@Prod.fst E' F₁) := contDiff_fst.contMDiff
  have hsnd : ContMDiff 𝓘(𝕜, E' × F₁) 𝓘(𝕜, F₁) n (@Prod.snd E' F₁) := contDiff_snd.contMDiff
  have hτF : ContMDiffOn 𝓘(𝕜, E' × F₁) 𝓘(𝕜, E' × F₁) n τF τF.source :=
    (hτ.comp hfst.contMDiffOn fun _ (hp : _ ∈ τ.source ×ˢ univ) ↦ hp.1).prodMk_space
      hsnd.contMDiffOn
  have hτFsymm : ContMDiffOn 𝓘(𝕜, E' × F₁) 𝓘(𝕜, E' × F₁) n τF.symm τF.target :=
    (hτsymm.comp hfst.contMDiffOn fun _ (hp : _ ∈ τ.target ×ˢ univ) ↦ hp.1).prodMk_space
      hsnd.contMDiffOn
  have hΘ : ContMDiffOn I 𝓘(𝕜, E) n Θ Θ.source :=
    hf.equiv.symm.contDiff.contMDiff.comp_contMDiffOn <|
      hτF.comp ((hf.equiv.contDiff.contMDiff.comp_contMDiffOn hΦ₁).mono inter_subset_left)
        fun _ hz ↦ hz.2
  have hΘsymm : ContMDiffOn 𝓘(𝕜, E) I n Θ.symm Θ.target := by
    have h₁ : ContMDiffOn 𝓘(𝕜, E' × F₁) I n (Φ₁.transHomeomorph hf.equiv.toHomeomorph).symm
        (Φ₁.transHomeomorph hf.equiv.toHomeomorph).target :=
      hΦ₁symm.comp hf.equiv.symm.contDiff.contMDiff.contMDiffOn fun _ hy ↦ hy
    have h₂ : ContMDiffOn 𝓘(𝕜, E' × F₁) I n
        ((Φ₁.transHomeomorph hf.equiv.toHomeomorph).trans τF).symm
        ((Φ₁.transHomeomorph hf.equiv.toHomeomorph).trans τF).target :=
      h₁.comp (hτFsymm.mono inter_subset_left) fun _ hz ↦ hz.2
    exact h₂.comp hf.equiv.contDiff.contMDiff.contMDiffOn fun _ hw ↦ hw
  have hφ : φ ∈ IsManifold.maximalAtlas I n M :=
    OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn _
      (hIsymm.comp_contMDiffOn hΘ)
      (hΘsymm.comp I.contMDiff.contMDiffOn fun _ hy ↦ hy)
  have hprojx : (hf.equiv (Φ₁ x)).1 = Ψ₁ (f x) := by
    simpa [Φ₁, Ψ₁, OpenPartialHomeomorph.extend_coe] using
      (hf.codChart_extend_apply hf.mem_domChart_source).symm
  have hxφ : x ∈ φ.source := by
    simp only [φ, Θ, τF, τ, Φ₂, OpenPartialHomeomorph.transHomeomorph_source,
      OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.prod_source,
      OpenPartialHomeomorph.refl_source, OpenPartialHomeomorph.symm_source,
      OpenPartialHomeomorph.transHomeomorph_apply, ContinuousLinearEquiv.coe_toHomeomorph,
      comp_apply, mem_inter_iff, mem_preimage, mem_prod, mem_univ, and_true]
    refine ⟨hf.mem_domChart_source, ?_⟩
    have hfxΨ₁ : f x ∈ Ψ₁.source := hf.mem_codChart_source
    rw [hprojx]
    exact ⟨Ψ₁.map_source hfxΨ₁, by rw [Ψ₁.left_inv hfxΨ₁]; exact hfx⟩
  have hmain : ∀ w ∈ (φ.extend I).target,
      (hf.equiv w).1 ∈ (ψ.extend J).target ∧
      f ((φ.extend I).symm w) = (ψ.extend J).symm (hf.equiv w).1 ∧
      ψ.extend J (f ((φ.extend I).symm w)) = (hf.equiv w).1 := by
    intro w hw
    have hIw : I (I.symm w) = w := I.right_inv (I.range_eq_univ.symm ▸ mem_univ w)
    have hwΘ : w ∈ Θ.target := by
      simpa [φ, OpenPartialHomeomorph.extend_target, hIw, I.range_eq_univ] using hw
    set u' : E' := (hf.equiv w).1
    set v₁ : F₁ := (hf.equiv w).2
    set z : E := hf.equiv.symm (τ.symm u', v₁)
    have hwΘ' : u' ∈ τ.target ∧ z ∈ (hf.domChart.extend I).target := by
      have heq : hf.equiv.symm.toHomeomorph.symm = hf.equiv.toHomeomorph := rfl
      simp only [Θ, τF, Φ₁, heq, OpenPartialHomeomorph.transHomeomorph_target,
        OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.prod_target,
        OpenPartialHomeomorph.refl_target, OpenPartialHomeomorph.prod_symm,
        OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.prod_apply,
        OpenPartialHomeomorph.refl_apply, ContinuousLinearEquiv.coe_toHomeomorph,
        I.toHomeomorph_symm_apply, mem_inter_iff, mem_preimage, mem_prod, mem_univ, and_true] at hwΘ
      refine ⟨hwΘ.1, ?_⟩
      rw [OpenPartialHomeomorph.extend_target, I.range_eq_univ, inter_univ]
      exact hwΘ.2
    obtain ⟨hu'τ, hzΦ₁⟩ := hwΘ'
    have hsymm : (φ.extend I).symm w = (hf.domChart.extend I).symm z := by
      simp [φ, Θ, τF, Φ₁, z, u', v₁, hIw]
    have hf_eq : hf.codChart.extend J (f ((hf.domChart.extend I).symm z)) = τ.symm u' := by
      simpa [z] using hf.writtenInCharts hzΦ₁
    have hfz_mem : f ((hf.domChart.extend I).symm z) ∈ (hf.codChart.extend J).source := by
      rw [OpenPartialHomeomorph.extend_source]
      exact hf.source_subset_preimage_source <| by
        rw [← hf.domChart.extend_source (I := I)]
        exact (hf.domChart.extend I).map_target hzΦ₁
    have hu'τ_mem : u' ∈ Φ₂.target ∧ Φ₂.symm u' ∈ Ψ₁.source := by
      simpa [τ] using hu'τ
    have hf_val : f ((φ.extend I).symm w) = (ψ.extend J).symm u' := by
      rw [hsymm]
      calc f ((hf.domChart.extend I).symm z)
          = (hf.codChart.extend J).symm
              (hf.codChart.extend J (f ((hf.domChart.extend I).symm z))) :=
            ((hf.codChart.extend J).left_inv hfz_mem).symm
        _ = Ψ₁.symm (τ.symm u') := by rw [hf_eq]; simp [Ψ₁]
        _ = Ψ₁.symm (Ψ₁ (Φ₂.symm u')) := rfl
        _ = Φ₂.symm u' := Ψ₁.left_inv hu'τ_mem.2
        _ = (ψ.extend J).symm u' := by simp [Φ₂]
    have hu'ψ : u' ∈ (ψ.extend J).target := by
      simpa [Φ₂, OpenPartialHomeomorph.extend_target, J.range_eq_univ] using hu'τ_mem.1
    exact ⟨hu'ψ, hf_val, by rw [hf_val]; exact (ψ.extend J).right_inv hu'ψ⟩
  refine ⟨φ, hxφ, hφ, fun y hy ↦ ?_, hmain⟩
  have hy' : y ∈ (φ.extend I).source := by rwa [φ.extend_source]
  obtain ⟨hu', hfy, -⟩ := hmain (φ.extend I y) ((φ.extend I).map_source hy')
  rw [mem_preimage, ← (φ.extend I).left_inv hy', hfy, ← ψ.extend_source (I := J)]
  exact (ψ.extend J).map_target hu'

/-- **Composition of submersions at a point, keeping track of complements.** If `f : M → N` is a
`C^n` submersion at `x` with complement `F₁` and `g : N → P` is a `C^n` submersion at `f x` with
complement `F₂`, and the models of `M` and `N` have no boundary, then `g ∘ f` is a `C^n` submersion
at `x` with complement `F₁ × F₂`. -/
theorem IsSubmersionAtOfComplement.comp
    (hg : IsSubmersionAtOfComplement F₂ J K n g (f x))
    (hf : IsSubmersionAtOfComplement F₁ I J n f x) :
    IsSubmersionAtOfComplement (F₁ × F₂) I K n (g ∘ f) x := by
  obtain ⟨φ, hxφ, hφ, -, hmain⟩ :=
    hf.exists_domChart_of_codChart hg.mem_domChart_source hg.domChart_mem_maximalAtlas
  have hcont : ContinuousAt (g ∘ f) x :=
    hg.contMDiffAt.continuousAt.comp hf.contMDiffAt.continuousAt
  let L : E ≃L[𝕜] E'' × (F₁ × F₂) :=
    hf.equiv.trans <|
      (hg.equiv.prodCongr (ContinuousLinearEquiv.refl 𝕜 F₁)).trans <|
        (ContinuousLinearEquiv.prodAssoc 𝕜 E'' F₂ F₁).trans <|
          (ContinuousLinearEquiv.refl 𝕜 E'').prodCongr (ContinuousLinearEquiv.prodComm 𝕜 F₂ F₁)
  refine .mk_of_continuousAt hcont L φ hg.codChart hxφ hg.mem_codChart_source
    hφ hg.codChart_mem_maximalAtlas fun w hw ↦ ?_
  obtain ⟨hu', hfw, -⟩ := hmain w hw
  calc hg.codChart.extend K ((g ∘ f) ((φ.extend I).symm w))
      = hg.codChart.extend K (g ((hg.domChart.extend J).symm (hf.equiv w).1)) := by
          rw [comp_apply, hfw]
    _ = (hg.equiv (hf.equiv w).1).1 := hg.writtenInCharts hu'
    _ = (L w).1 := by simp [L]

/-- **Composition of submersions at a point.** If `f : M → N` is a `C^n` submersion at `x` and
`g : N → P` is a `C^n` submersion at `f x`, with boundaryless models on `M` and `N`, then `g ∘ f`
is a `C^n` submersion at `x`. -/
theorem IsSubmersionAt.comp (hg : IsSubmersionAt J K n g (f x))
    (hf : IsSubmersionAt I J n f x) :
    IsSubmersionAt I K n (g ∘ f) x :=
  (hg.isSubmersionAtOfComplement_complement.comp
    hf.isSubmersionAtOfComplement_complement).isSubmersionAt

/-- **Composition of submersions with fixed complements.** -/
theorem IsSubmersionOfComplement.comp
    (hg : IsSubmersionOfComplement F₂ J K n g)
    (hf : IsSubmersionOfComplement F₁ I J n f) :
    IsSubmersionOfComplement (F₁ × F₂) I K n (g ∘ f) :=
  isSubmersionOfComplement_iff.mpr fun x ↦ (hg.isSubmersionAt (f x)).comp (hf.isSubmersionAt x)

/-- **Composition of submersions.** When the source and intermediate models have no boundary, the
composite of two `C^n` submersions is a `C^n` submersion. -/
theorem IsSubmersion.comp (hg : IsSubmersion J K n g) (hf : IsSubmersion I J n f) :
    IsSubmersion I K n (g ∘ f) :=
  (hg.isSubmersionOfComplement_complement.comp
    hf.isSubmersionOfComplement_complement).isSubmersion

end Composition

section Transversality

variable {𝕜 EX HX X EY HY Y EN HN N : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup EX] [NormedSpace 𝕜 EX] [TopologicalSpace HX]
  [NormedAddCommGroup EY] [NormedSpace 𝕜 EY] [TopologicalSpace HY]
  [NormedAddCommGroup EN] [NormedSpace 𝕜 EN] [TopologicalSpace HN]
  {IX : ModelWithCorners 𝕜 EX HX} {IY : ModelWithCorners 𝕜 EY HY}
  {IN : ModelWithCorners 𝕜 EN HN}
  [TopologicalSpace X] [ChartedSpace HX X]
  [TopologicalSpace Y] [ChartedSpace HY Y]
  [TopologicalSpace N] [ChartedSpace HN N]
  {n : ℕ∞ω} {f : X → N} {g : Y → N}

/-- A map which is a `C^n` submersion (`n ≠ 0`) at `p.1` is transverse there to every map `g` from
the right factor: the differential of `f` alone spans the target tangent space. -/
theorem IsSubmersionAt.transverse_left {p : X × Y} (hf : IsSubmersionAt IX IN n f p.1)
    (hn : n ≠ 0) (g : Y → N) :
    (mfderiv IX IN f p.1).range ⊔
      (((tangentSpaceCast IN (g p.2) (f p.1)).toContinuousLinearMap).comp
        (mfderiv IY IN g p.2)).range = ⊤ := by
  rw [LinearMap.range_eq_top.2 (hf.surjective_mfderiv hn), top_sup_eq]

/-- A `C^n` submersion (`n ≠ 0`) in the first factor is transverse to every map in the second
factor. -/
theorem IsSubmersion.transverse_left (hf : IsSubmersion IX IN n f) (hn : n ≠ 0) (g : Y → N)
    (p : X × Y) :
    (mfderiv IX IN f p.1).range ⊔
      (((tangentSpaceCast IN (g p.2) (f p.1)).toContinuousLinearMap).comp
        (mfderiv IY IN g p.2)).range = ⊤ :=
  (hf.isSubmersionAt p.1).transverse_left hn g

/-- A map which is a `C^n` submersion (`n ≠ 0`) at `p.2` is transverse there to every map `f` from
the left factor: the differential of `g`, transported by `tangentSpaceCast`, spans the target
tangent space. -/
theorem IsSubmersionAt.transverse_right (f : X → N) {p : X × Y}
    (hg : IsSubmersionAt IY IN n g p.2) (hn : n ≠ 0) :
    (mfderiv IX IN f p.1).range ⊔
      (((tangentSpaceCast IN (g p.2) (f p.1)).toContinuousLinearMap).comp
        (mfderiv IY IN g p.2)).range = ⊤ := by
  have hsurj : Surjective (((tangentSpaceCast IN (g p.2) (f p.1)).toContinuousLinearMap).comp
      (mfderiv IY IN g p.2)) :=
    (tangentSpaceCast IN (g p.2) (f p.1)).surjective.comp (hg.surjective_mfderiv hn)
  rw [LinearMap.range_eq_top.2 hsurj, sup_top_eq]

/-- A `C^n` submersion (`n ≠ 0`) in the second factor is transverse to every map in the first
factor. -/
theorem IsSubmersion.transverse_right (f : X → N) (hg : IsSubmersion IY IN n g) (hn : n ≠ 0)
    (p : X × Y) :
    (mfderiv IX IN f p.1).range ⊔
      (((tangentSpaceCast IN (g p.2) (f p.1)).toContinuousLinearMap).comp
        (mfderiv IY IN g p.2)).range = ⊤ :=
  (hg.isSubmersionAt p.2).transverse_right f hn

end Transversality

end Manifold

section LocalDiffeomorph

variable {𝕜 E E' H G M N : Type*} [NontriviallyNormedField 𝕜] {n : ℕ∞ω}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' G}
  [I.Boundaryless] [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I n M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J n N]

/-- A `C^n` local diffeomorphism at `x` (`n ≠ 0`) between boundaryless manifolds — even with
distinct model spaces — is a submersion at `x` with complement `PUnit`. Its invertible differential
at `x` supplies the linear isomorphism between the two model vector spaces. -/
theorem IsLocalDiffeomorphAt.isSubmersionAtOfComplement {f : M → N} {x : M}
    (hf : IsLocalDiffeomorphAt I J n f x) (hn : n ≠ 0) :
    Manifold.IsSubmersionAtOfComplement PUnit.{1} I J n f x := by
  have hcont : ContinuousAt f x := hf.contMDiffAt.continuousAt
  obtain ⟨L₀⟩ : Nonempty (E ≃L[𝕜] E') :=
    ⟨(tangentSpaceCastModel I x).symm.trans <|
      (hf.mfderivToContinuousLinearEquiv hn).trans (tangentSpaceCastModel J (f x))⟩
  obtain ⟨Θ, hxΘ, hfΘ⟩ := hf
  let ψ := chartAt G (f x)
  have hψ : ψ ∈ IsManifold.maximalAtlas J n N := IsManifold.chart_mem_maximalAtlas (f x)
  let Ψ : OpenPartialHomeomorph N E' := ψ.transHomeomorph J.toHomeomorph
  let Ξ : OpenPartialHomeomorph M E :=
    (Θ.toOpenPartialHomeomorph.trans Ψ).transHomeomorph L₀.symm.toHomeomorph
  let φ : OpenPartialHomeomorph M H := Ξ.transHomeomorph I.toHomeomorph.symm
  have hIsymm : ContMDiff 𝓘(𝕜, E) I n I.symm :=
    contMDiffOn_univ.1 (I.range_eq_univ ▸ I.contMDiffOn_symm)
  have hΨ := Manifold.contMDiffOn_transHomeomorph_toHomeomorph hψ
  have hΨsymm := Manifold.contMDiffOn_transHomeomorph_toHomeomorph_symm hψ
  have hΞ : ContMDiffOn I 𝓘(𝕜, E) n Ξ Ξ.source :=
    L₀.symm.contDiff.contMDiff.comp_contMDiffOn <|
      hΨ.comp (Θ.contMDiffOn.mono inter_subset_left) fun _ hz ↦ hz.2
  have hΞsymm : ContMDiffOn 𝓘(𝕜, E) I n Ξ.symm Ξ.target :=
    (Θ.symm.contMDiffOn.comp (hΨsymm.mono inter_subset_left) fun _ hz ↦ hz.2).comp
      L₀.contDiff.contMDiff.contMDiffOn fun _ hu ↦ hu
  have hφ : φ ∈ IsManifold.maximalAtlas I n M :=
    OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn _
      (hIsymm.comp_contMDiffOn hΞ)
      (hΞsymm.comp I.contMDiff.contMDiffOn fun _ hy ↦ hy)
  have hxφ : x ∈ φ.source := by
    simp only [φ, Ξ, Ψ, OpenPartialHomeomorph.transHomeomorph_source,
      OpenPartialHomeomorph.trans_source, PartialDiffeomorph.toOpenPartialHomeomorph_source,
      PartialDiffeomorph.toFun'_toOpenPartialHomeomorph, mem_inter_iff, mem_preimage]
    exact ⟨hxΘ, by rw [← hfΘ hxΘ]; exact mem_chart_source G (f x)⟩
  let L : E ≃L[𝕜] E' × PUnit.{1} := L₀.trans (ContinuousLinearEquiv.prodUnique 𝕜 E' PUnit.{1}).symm
  refine .mk_of_continuousAt hcont L φ ψ hxφ (mem_chart_source G (f x))
    hφ hψ fun u hu ↦ ?_
  have hIu : I (I.symm u) = u := I.right_inv (I.range_eq_univ.symm ▸ mem_univ u)
  have huΞ : u ∈ Ξ.target := by
    simpa [φ, OpenPartialHomeomorph.extend_target, hIu, I.range_eq_univ] using hu
  have huΞ' : L₀ u ∈ (ψ.extend J).target ∧ (ψ.extend J).symm (L₀ u) ∈ Θ.target := by
    have hL₀ : L₀.symm.toHomeomorph.symm = L₀.toHomeomorph := rfl
    simp only [Ξ, Ψ, hL₀, OpenPartialHomeomorph.transHomeomorph_target,
      OpenPartialHomeomorph.trans_target, PartialDiffeomorph.toOpenPartialHomeomorph_target,
      ContinuousLinearEquiv.coe_toHomeomorph, J.toHomeomorph_symm_apply, mem_inter_iff,
      mem_preimage] at huΞ
    refine ⟨?_, ?_⟩
    · rw [OpenPartialHomeomorph.extend_target, J.range_eq_univ, inter_univ]
      exact huΞ.1
    · simpa using huΞ.2
  obtain ⟨huΨ, hyΘ⟩ := huΞ'
  have hsymm : (φ.extend I).symm u = Θ.toPartialEquiv.symm ((ψ.extend J).symm (L₀ u)) := by
    simp [φ, Ξ, Ψ, hIu]
  have hf_apply : f ((φ.extend I).symm u) = (ψ.extend J).symm (L₀ u) := by
    rw [hsymm, hfΘ (Θ.toPartialEquiv.map_target hyΘ), Θ.toPartialEquiv.right_inv hyΘ]
  calc ψ.extend J (f ((φ.extend I).symm u))
      = ψ.extend J ((ψ.extend J).symm (L₀ u)) := by rw [hf_apply]
    _ = L₀ u := (ψ.extend J).right_inv huΨ
    _ = (L u).1 := rfl

/-- A `C^n` local diffeomorphism at `x` (`n ≠ 0`) between boundaryless manifolds is a submersion at
`x`. -/
theorem IsLocalDiffeomorphAt.isSubmersionAt {f : M → N} {x : M}
    (hf : IsLocalDiffeomorphAt I J n f x) (hn : n ≠ 0) :
    Manifold.IsSubmersionAt I J n f x :=
  (hf.isSubmersionAtOfComplement hn).isSubmersionAt

/-- A `C^n` local diffeomorphism (`n ≠ 0`) between boundaryless manifolds is a submersion with
complement `PUnit`. Empty domains are allowed. -/
theorem IsLocalDiffeomorph.isSubmersionOfComplement {f : M → N}
    (hf : IsLocalDiffeomorph I J n f) (hn : n ≠ 0) :
    Manifold.IsSubmersionOfComplement PUnit.{1} I J n f :=
  Manifold.isSubmersionOfComplement_iff.mpr fun x ↦ (hf x).isSubmersionAtOfComplement hn

/-- A `C^n` local diffeomorphism (`n ≠ 0`) between boundaryless manifolds is a submersion. -/
theorem IsLocalDiffeomorph.isSubmersion {f : M → N}
    (hf : IsLocalDiffeomorph I J n f) (hn : n ≠ 0) :
    Manifold.IsSubmersion I J n f :=
  (hf.isSubmersionOfComplement hn).isSubmersion

/-- A `C^n` diffeomorphism (`n ≠ 0`) between boundaryless manifolds is a submersion with complement
`PUnit`. -/
theorem Diffeomorph.isSubmersionOfComplement (Φ : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0) :
    Manifold.IsSubmersionOfComplement PUnit.{1} I J n Φ :=
  Φ.isLocalDiffeomorph.isSubmersionOfComplement hn

/-- A `C^n` diffeomorphism (`n ≠ 0`) between boundaryless manifolds is a submersion. -/
theorem Diffeomorph.isSubmersion (Φ : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0) :
    Manifold.IsSubmersion I J n Φ :=
  Φ.isLocalDiffeomorph.isSubmersion hn

end LocalDiffeomorph
