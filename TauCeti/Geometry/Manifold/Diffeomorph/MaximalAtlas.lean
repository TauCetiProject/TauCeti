/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.HasGroupoid
import TauCeti.Geometry.Manifold.Diffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions

/-!
# Maximal atlases under structomorphisms and diffeomorphisms

A `G`-structomorphism `e : M → M'` pulls the charts of the maximal `G`-atlas of `M'` back to charts
of the maximal `G`-atlas of `M`: for `φ` in the maximal atlas of `M'`, the chart `e ≫ φ` is in the
maximal atlas of `M` (`Structomorph.trans_mem_maximalAtlas`). The same holds for a `C^n`
diffeomorphism and the maximal `C^m` atlases, `m ≤ n`. So the charts of the two maximal atlases
correspond, with the same targets and inverses related by `e`
(`Structomorph.exists_mem_maximalAtlas_symm_eq_comp`,
`Diffeomorph.exists_mem_maximalAtlas_comp_symm_eq`,
`Diffeomorph.exists_mem_maximalAtlas_symm_eq_comp`): anything defined by testing every chart of a
maximal atlas is invariant under structomorphisms and diffeomorphisms.

## Main results

* `Structomorph.symm_toHomeomorph`: the homeomorphism underlying the inverse structomorphism.
* `Structomorph.symm_trans_trans_mem_of_mem_maximalAtlas`: read in a chart of `M` and a chart of
  the maximal atlas of `M'`, a structomorphism is in `G`.
* `Structomorph.trans_mem_maximalAtlas`: the pullback `e ≫ φ` of a chart of the maximal atlas.
* `Structomorph.exists_mem_maximalAtlas_symm_eq_comp`,
  `Diffeomorph.exists_mem_maximalAtlas_comp_symm_eq`,
  `Diffeomorph.exists_mem_maximalAtlas_symm_eq_comp`: corresponding charts of the two maximal
  atlases.
-/

public section

open Set OpenPartialHomeomorph
open scoped Manifold

namespace Structomorph

variable {H : Type*} [TopologicalSpace H] {G : StructureGroupoid H}
  {M M' : Type*} [TopologicalSpace M] [TopologicalSpace M'] [ChartedSpace H M] [ChartedSpace H M']

/-- The homeomorphism underlying the inverse of a structomorphism is the inverse homeomorphism. -/
@[simp]
theorem symm_toHomeomorph (e : Structomorph G M M') : e.symm.toHomeomorph = e.toHomeomorph.symm :=
  rfl

/-- Read in a chart `c` of the atlas of `M` and a chart `φ` of the maximal `G`-atlas of `M'`, a
`G`-structomorphism `e : M → M'` is in `G`: near each point it is `e` read in `c` and a chart `g`
of `M'`, followed by the coordinate change `g⁻¹ ≫ φ`. -/
theorem symm_trans_trans_mem_of_mem_maximalAtlas (e : Structomorph G M M')
    {c : OpenPartialHomeomorph M H} (hc : c ∈ atlas H M) {φ : OpenPartialHomeomorph M' H}
    (hφ : φ ∈ G.maximalAtlas M') :
    c.symm ≫ₕ e.toHomeomorph.toOpenPartialHomeomorph ≫ₕ φ ∈ G := by
  refine G.locality fun x hx ↦ ?_
  let f := e.toHomeomorph.toOpenPartialHomeomorph
  let g := chartAt H ((c.symm ≫ₕ f) x)
  let s := (c.symm ≫ₕ f).source ∩ (c.symm ≫ₕ f) ⁻¹' g.source
  have hs : IsOpen s :=
    (c.symm ≫ₕ f).continuousOn_toFun.isOpen_inter_preimage (open_source _) (open_source _)
  have hxs : x ∈ s := by
    refine ⟨?_, mem_chart_source H _⟩
    simp only [f, trans_source, preimage_univ, inter_univ,
      Homeomorph.toOpenPartialHomeomorph_source]
    rw [trans_source] at hx
    exact hx.1
  refine ⟨s, hs, hxs, ?_⟩
  have hA : (c.symm ≫ₕ f ≫ₕ g) ≫ₕ g.symm ≫ₕ φ ∈ G :=
    G.trans (e.mem_groupoid c g hc (chart_mem_atlas H _)) (hφ g (chart_mem_atlas H _)).2
  have heq : (c.symm ≫ₕ f ≫ₕ g) ≫ₕ g.symm ≫ₕ φ ≈ (c.symm ≫ₕ f ≫ₕ φ).restr s := calc
    _ ≈ c.symm ≫ₕ f ≫ₕ (g ≫ₕ g.symm) ≫ₕ φ := by simp only [trans_assoc, _root_.refl]
    _ ≈ c.symm ≫ₕ f ≫ₕ ofSet g.source g.open_source ≫ₕ φ :=
      EqOnSource.trans' (_root_.refl _) (EqOnSource.trans' (_root_.refl _)
        (EqOnSource.trans' (self_trans_symm g) (_root_.refl _)))
    _ ≈ ((c.symm ≫ₕ f) ≫ₕ ofSet g.source g.open_source) ≫ₕ φ := by
      simp only [trans_assoc, _root_.refl]
    _ ≈ (c.symm ≫ₕ f).restr s ≫ₕ φ := by rw [trans_of_set']
    _ ≈ ((c.symm ≫ₕ f) ≫ₕ φ).restr s := by rw [restr_trans]
    _ ≈ (c.symm ≫ₕ f ≫ₕ φ).restr s := by simp only [trans_assoc, _root_.refl]
  exact G.mem_of_eqOnSource hA (Setoid.symm heq)

/-- **Pulling back charts of the maximal atlas.** For a `G`-structomorphism `e : M → M'` and a
chart `φ` of the maximal `G`-atlas of `M'`, the chart `e ≫ φ` is in the maximal `G`-atlas of
`M`. -/
theorem trans_mem_maximalAtlas (e : Structomorph G M M') {φ : OpenPartialHomeomorph M' H}
    (hφ : φ ∈ G.maximalAtlas M') :
    e.toHomeomorph.toOpenPartialHomeomorph ≫ₕ φ ∈ G.maximalAtlas M := by
  intro c hc
  have h := e.symm_trans_trans_mem_of_mem_maximalAtlas hc hφ
  refine ⟨?_, h⟩
  have h' := G.symm h
  rwa [trans_symm_eq_symm_trans_symm, symm_symm] at h'

/-- **Corresponding charts.** For a `G`-structomorphism `e : M → M'`, every chart `φ'` of the
maximal `G`-atlas of `M` corresponds to a chart `φ` of the maximal `G`-atlas of `M'`, namely
`e⁻¹ ≫ φ'`, with the same target and with `φ⁻¹ = e ∘ φ'⁻¹`. -/
theorem exists_mem_maximalAtlas_symm_eq_comp (e : Structomorph G M M')
    {φ' : OpenPartialHomeomorph M H} (hφ' : φ' ∈ G.maximalAtlas M) :
    ∃ φ ∈ G.maximalAtlas M', φ.target = φ'.target ∧ φ.symm = e.toHomeomorph ∘ φ'.symm := by
  refine ⟨_, e.symm.trans_mem_maximalAtlas hφ', ?_, ?_⟩
  · rw [trans_target]
    exact inter_univ _
  · simp [coe_trans_symm]

end Structomorph

namespace Diffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] {m n : WithTop ℕ∞}

/-- A chart `φ` of the maximal `C^m` atlas of `N` pulls back along a `C^n` diffeomorphism
`f : M → N`, for `m ≤ n`, to a chart `φ'` of the maximal `C^m` atlas of `M` with the same target
and with `f ∘ φ'⁻¹ = φ⁻¹`, namely `f ≫ φ`. -/
theorem exists_mem_maximalAtlas_comp_symm_eq [IsManifold I m M] (f : M ≃ₘ^n⟮I, I⟯ N)
    (hmn : m ≤ n) {φ : OpenPartialHomeomorph N H} (hφ : φ ∈ IsManifold.maximalAtlas I m N) :
    ∃ φ' ∈ IsManifold.maximalAtlas I m M, φ'.target = φ.target ∧ f ∘ φ'.symm = φ.symm := by
  have hΦ : (f.toPartialDiffeomorph.ofLE hmn).toOpenPartialHomeomorph =
      f.toHomeomorph.toOpenPartialHomeomorph := by
    ext x <;> simp
  have hφ' := (f.toPartialDiffeomorph.ofLE hmn).trans_mem_maximalAtlas hφ
  rw [hΦ] at hφ'
  refine ⟨_, hφ', ?_, ?_⟩
  · rw [OpenPartialHomeomorph.trans_target]
    exact inter_univ _
  · rw [OpenPartialHomeomorph.coe_trans_symm]
    funext z
    exact f.apply_symm_apply _

/-- A chart `φ'` of the maximal `C^m` atlas of `M` corresponds, for a `C^n` diffeomorphism
`f : M → N` with `m ≤ n`, to a chart `φ` of the maximal `C^m` atlas of `N` with the same target
and with `φ⁻¹ = f ∘ φ'⁻¹`, namely `f⁻¹ ≫ φ'`. -/
theorem exists_mem_maximalAtlas_symm_eq_comp [IsManifold I m N] (f : M ≃ₘ^n⟮I, I⟯ N)
    (hmn : m ≤ n) {φ' : OpenPartialHomeomorph M H} (hφ' : φ' ∈ IsManifold.maximalAtlas I m M) :
    ∃ φ ∈ IsManifold.maximalAtlas I m N, φ.target = φ'.target ∧ φ.symm = f ∘ φ'.symm := by
  obtain ⟨φ, hφ, htarget, hcomp⟩ := f.symm.exists_mem_maximalAtlas_comp_symm_eq hmn hφ'
  refine ⟨φ, hφ, htarget, ?_⟩
  rw [← hcomp]
  funext z
  exact (f.apply_symm_apply _).symm

end Diffeomorph
