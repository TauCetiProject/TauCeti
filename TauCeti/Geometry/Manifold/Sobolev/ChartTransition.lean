/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import TauCeti.Analysis.Sobolev.Local.Basic
public import TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic.Basic
import TauCeti.Analysis.Calculus.FDeriv.Equiv
import TauCeti.Analysis.Sobolev.Local.ChangeOfVariables
import TauCeti.Analysis.Sobolev.Local.ChangeOfVariables.Higher
import TauCeti.Geometry.Manifold.Complex.ClosedUpperHalfPlane
import TauCeti.Geometry.Manifold.MFDeriv.ModelChart
import TauCeti.Geometry.Manifold.Complex.Analytic
import TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic.Double

/-!
# Local Sobolev classes under changes of chart

Let `M` be a `C¹` manifold without boundary modelled on `ℂ`. A transition map `φ.symm.trans ψ`
between two charts of the maximal `C¹` atlas of `M` is a `C¹` diffeomorphism between open planar
sets, so composing with it preserves the local Sobolev classes `TauCeti.MemWkpLoc` of order at most
one, by the planar change of variables `TauCeti.MemWkpLoc.comp_contDiffOn_diffeo`.

On a `Cⁿ` manifold, `n ≠ 0`, a transition map between two charts of the maximal `Cⁿ` atlas is a
`Cⁿ` map with invertible derivative on its open source, so composing with it also preserves the
local classes on open sets of every order `k ≤ n`, for `1 ≤ p ≤ ∞` and maps into a
finite-dimensional space, by the planar change of variables of every order
`TauCeti.MemWkpLoc.comp_contDiffOn`.

## Main results

* `TauCeti.MemWkpLoc.comp_symm_trans_of_mem_maximalAtlas`: changes of chart preserve the local
  classes of order at most one.
* `TauCeti.MemWkpLoc.comp_symm_trans_of_mem_maximalAtlas_of_le`: changes of chart in the maximal
  `Cⁿ` atlas preserve the local classes on open sets of every order `k ≤ n`, provided `k ≤ 1` or
  `1 ≤ p`.
* `TauCeti.exists_extension_bordered_transition`: a change of bordered holomorphic chart, read in
  the extended charts, is the restriction to the closed upper half-plane of a holomorphic chart
  change of `ℂ`, its Schwarz reflection.
* `TauCeti.memWkpLoc_comp_bordered_transition`: on a Riemann surface with boundary, changes of
  bordered holomorphic chart preserve the local classes of order at most one on subsets of the
  closed upper half-plane, through the Schwarz reflection of the transition map.
* `TauCeti.MemWkpLoc.comp_bordered_transition`: for `1 ≤ p ≤ ∞`, they preserve the local classes
  of every order of maps into a finite-dimensional space on the half-discs over open sets.
-/

public section

open Set TopologicalSpace
open scoped Manifold ENNReal

namespace TauCeti

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℝ≥0∞} {k : ℕ} {n : WithTop ℕ∞}

/-- **Changes of chart preserve the local classes of order at most one.** For charts `φ` and `ψ`
of the maximal `C¹` atlas of `M` and a map `u` in `MemWkpLoc p U k` with `k ≤ 1`, the map
`u ∘ ψ ∘ φ.symm` lies in the local class on the set of points of the source of the chart transition
`φ.symm.trans ψ` that it maps into `U`. -/
theorem MemWkpLoc.comp_symm_trans_of_mem_maximalAtlas (hk : k ≤ 1)
    {φ ψ : OpenPartialHomeomorph M ℂ} (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, ℂ) 1 M)
    (hψ : ψ ∈ IsManifold.maximalAtlas 𝓘(ℝ, ℂ) 1 M) {U : Set ℂ} {u : ℂ → F}
    (hu : MemWkpLoc p U k u) :
    MemWkpLoc p ((φ.symm.trans ψ).source ∩ φ.symm.trans ψ ⁻¹' U) k
      (fun y ↦ u (ψ (φ.symm y))) := by
  -- As a function, the chart transition is `ψ ∘ φ.symm` (`OpenPartialHomeomorph.coe_trans`).
  simpa only [OpenPartialHomeomorph.coe_trans, Function.comp_apply] using
    hu.comp_contDiffOn_diffeo hk (φ.symm.trans ψ).open_source
      (contDiffOn_symm_trans_of_mem_maximalAtlas hφ hψ)
      ((φ.symm.trans ψ).injOn.mono inter_subset_left)
      (fun y hy ↦ det_fderiv_symm_trans_ne_zero one_ne_zero hφ hψ hy.1) inter_subset_left
      fun y hy ↦ hy.2

/-- **Changes of chart preserve the local classes of every order.** Let `n ≠ 0` and `k ≤ n`, and
let either `k ≤ 1` or `1 ≤ p`. For charts `φ` and `ψ` of the maximal `Cⁿ` atlas of `M` and a
map `u` into a finite-dimensional space in `MemWkpLoc p U k` on an open set `U`, the map
`u ∘ ψ ∘ φ.symm` lies in the local class on the set of points of the source of the chart transition
`φ.symm.trans ψ` that it maps into `U`. Orders `k ≤ 1` reduce to
`TauCeti.MemWkpLoc.comp_symm_trans_of_mem_maximalAtlas`, which needs neither the openness of `U`
nor the finite dimension. -/
theorem MemWkpLoc.comp_symm_trans_of_mem_maximalAtlas_of_le [FiniteDimensional ℝ F]
    {φ ψ : OpenPartialHomeomorph M ℂ} (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, ℂ) n M)
    (hψ : ψ ∈ IsManifold.maximalAtlas 𝓘(ℝ, ℂ) n M) {U : Set ℂ} (hU : IsOpen U) {u : ℂ → F}
    (hu : MemWkpLoc p U k u) (hkp : k ≤ 1 ∨ 1 ≤ p) (hn : n ≠ 0)
    (hkn : (k : WithTop ℕ∞) ≤ n) :
    MemWkpLoc p ((φ.symm.trans ψ).source ∩ φ.symm.trans ψ ⁻¹' U) k
      (fun y ↦ u (ψ (φ.symm y))) := by
  rcases le_or_gt k 1 with hk | hk
  · have h₁ := IsManifold.maximalAtlas_subset_of_le (I := 𝓘(ℝ, ℂ)) (M := M)
      (ENat.one_le_iff_ne_zero_withTop.2 hn)
    exact hu.comp_symm_trans_of_mem_maximalAtlas hk (h₁ hφ) (h₁ hψ)
  have : Fact (1 ≤ p) := ⟨hkp.resolve_left hk.not_ge⟩
  -- As a function, the chart transition is `ψ ∘ φ.symm` (`OpenPartialHomeomorph.coe_trans`).
  simpa only [OpenPartialHomeomorph.coe_trans, Function.comp_apply, Opens.coe_mk] using
    hu.comp_contDiffOn (U := ⟨_, (φ.symm.trans ψ).isOpen_inter_preimage hU⟩) (V := ⟨U, hU⟩)
      hk.le
      (((contDiffOn_symm_trans_of_mem_maximalAtlas hφ hψ).of_le hkn).mono inter_subset_left)
      (fun y hy ↦ det_fderiv_symm_trans_ne_zero hn hφ hψ hy.1) fun y hy ↦ hy.2

section Bordered

open ClosedUpperHalfPlane

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ClosedUpperHalfPlane X]

/-! ### Change of bordered holomorphic chart -/

/-- **The Schwarz reflection of a change of bordered holomorphic chart.** For two bordered
holomorphic charts `φ` and `φ'`, there is a holomorphic chart change `Φ` of `ℂ` that is defined on
the part of the extended target of `φ'` over the source of `φ` and agrees with the transition map
`φ ∘ φ'⁻¹`, read in the extended charts, on the closed upper half-plane. It is the Schwarz
reflection `TauCeti.ClosedUpperHalfPlane.schwarzDouble` of `φ'⁻¹ ≫ φ`. -/
theorem exists_extension_bordered_transition {φ φ' : OpenPartialHomeomorph X ClosedUpperHalfPlane}
    (hφ : φ ∈ borderedHolomorphicGroupoid.maximalAtlas X)
    (hφ' : φ' ∈ borderedHolomorphicGroupoid.maximalAtlas X) :
    ∃ Φ : OpenPartialHomeomorph ℂ ℂ, Φ ∈ contDiffGroupoid (⊤ : WithTop ℕ∞) 𝓘(ℂ) ∧
      (φ'.extend closedUpperHalfPlaneModel).target ∩
          (φ'.extend closedUpperHalfPlaneModel).symm ⁻¹' φ.source ⊆ Φ.source ∧
      ∀ z : ℂ, 0 ≤ z.im → Φ z =
        (φ.extend closedUpperHalfPlaneModel ∘ (φ'.extend closedUpperHalfPlaneModel).symm) z := by
  set e := φ'.symm ≫ₕ φ
  have he : e ∈ borderedHolomorphicGroupoid :=
    StructureGroupoid.compatible_of_mem_maximalAtlas hφ' hφ
  have hre : PreservesRealAxis e := preservesRealAxis_of_mem_borderedHolomorphicGroupoid he
  refine ⟨schwarzDouble e hre, schwarzDouble_mem_contDiffGroupoid hre he, fun z hz ↦ ?_,
    fun z hz ↦ ?_⟩
  · have hupper : 0 ≤ z.im := by simpa using φ'.extend_target_subset_range hz.1
    obtain ⟨hzt, hzφ⟩ := hz
    rw [OpenPartialHomeomorph.extend_target] at hzt
    simp only [mem_preimage, OpenPartialHomeomorph.extend_coe_symm, Function.comp_apply] at hzφ
    simp only [e, schwarzDouble_source, mem_preimage, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.symm_source, mem_inter_iff,
      ← closedUpperHalfPlaneModel_symm_eq_fold hupper]
    exact ⟨hzt.1, hzφ⟩
  · -- On the closed upper half-plane the reflection is the transition map.
    rw [schwarzDouble_apply_of_im_nonneg hre hz]
    simp [e, closedUpperHalfPlaneModel_symm_eq_fold hz]

/-- **Change of bordered holomorphic chart.** Precomposition with the transition map
`φ ∘ φ'⁻¹` between two bordered holomorphic charts preserves the planar classes of order at most
one on subsets of the overlap. The transition map is read through its Schwarz
reflection, a holomorphic chart of `ℂ` agreeing with it on the closed upper half-plane. -/
theorem memWkpLoc_comp_bordered_transition
    {φ φ' : OpenPartialHomeomorph X ClosedUpperHalfPlane}
    (hφ : φ ∈ borderedHolomorphicGroupoid.maximalAtlas X)
    (hφ' : φ' ∈ borderedHolomorphicGroupoid.maximalAtlas X)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : ℂ → E} {V W : Set ℂ} (hk : k ≤ 1)
    (hg : MemWkpLoc p V k g)
    (hWφ : W ⊆ (φ'.extend closedUpperHalfPlaneModel).target ∩
      (φ'.extend closedUpperHalfPlaneModel).symm ⁻¹' φ.source)
    (hmaps : MapsTo (φ.extend closedUpperHalfPlaneModel ∘
      (φ'.extend closedUpperHalfPlaneModel).symm) W V) :
    MemWkpLoc p W k
      (g ∘ φ.extend closedUpperHalfPlaneModel ∘ (φ'.extend closedUpperHalfPlaneModel).symm) := by
  obtain ⟨Φ, hΦω, hsub, hagree⟩ := exists_extension_bordered_transition hφ hφ'
  have hΦ : Φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 ℂ :=
    (contDiffGroupoid 1 𝓘(ℂ)).mem_maximalAtlas_of_mem_groupoid
      (contDiffGroupoid_le (by exact_mod_cast le_top) hΦω)
  have hupper : ∀ z ∈ W, 0 ≤ z.im := fun z hz ↦ by
    simpa using φ'.extend_target_subset_range (hWφ hz).1
  refine ((hg.comp_symm_trans_of_mem_maximalAtlas hk
    (contDiffGroupoid 1 𝓘(ℝ, ℂ)).id_mem_maximalAtlas
    (IsManifold.maximalAtlas_subset_restrictScalars_of_ne_zero 1 one_ne_zero hΦ)).mono
      fun z hz ↦ ⟨⟨mem_univ z, hsub (hWφ hz)⟩, ?_⟩).congr fun z hz ↦ ?_
  · simpa only [mem_preimage, OpenPartialHomeomorph.coe_trans, Function.comp_apply,
      OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_apply, id_eq,
      hagree z (hupper z hz)] using hmaps hz
  · simp only [Function.comp_apply, OpenPartialHomeomorph.refl_symm,
      OpenPartialHomeomorph.refl_apply, id_eq]
    rw [hagree z (hupper z hz), Function.comp_apply]

/-- **Change of bordered holomorphic chart at every order.** For `1 ≤ p ≤ ∞` and every order `k`,
precomposition with the transition map `φ ∘ φ'⁻¹` between two bordered holomorphic charts
preserves the local classes of order `k`, on the half-discs over open sets, of maps into a
finite-dimensional space. The transition map is read through its Schwarz reflection, a holomorphic
map with invertible derivative that preserves the closed upper half-plane, so the half-disc change
of variables `TauCeti.MemWkpLoc.comp_contDiffOn_halfPlane` applies. -/
theorem MemWkpLoc.comp_bordered_transition [Fact (1 ≤ p)]
    {φ φ' : OpenPartialHomeomorph X ClosedUpperHalfPlane}
    (hφ : φ ∈ borderedHolomorphicGroupoid.maximalAtlas X)
    (hφ' : φ' ∈ borderedHolomorphicGroupoid.maximalAtlas X)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {g : ℂ → E}
    {T T' : Set X} (hT : IsOpen T) (hT' : IsOpen T')
    (hg : MemWkpLoc p ((φ.extend closedUpperHalfPlaneModel).target ∩
      (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' T) k g)
    (hW : (φ'.extend closedUpperHalfPlaneModel).target ∩
        (φ'.extend closedUpperHalfPlaneModel).symm ⁻¹' T' ⊆
      (φ'.extend closedUpperHalfPlaneModel).target ∩
        (φ'.extend closedUpperHalfPlaneModel).symm ⁻¹' φ.source)
    (hmaps : MapsTo (φ.extend closedUpperHalfPlaneModel ∘
        (φ'.extend closedUpperHalfPlaneModel).symm)
      ((φ'.extend closedUpperHalfPlaneModel).target ∩
        (φ'.extend closedUpperHalfPlaneModel).symm ⁻¹' T')
      ((φ.extend closedUpperHalfPlaneModel).target ∩
        (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' T)) :
    MemWkpLoc p ((φ'.extend closedUpperHalfPlaneModel).target ∩
        (φ'.extend closedUpperHalfPlaneModel).symm ⁻¹' T') k
      (g ∘ φ.extend closedUpperHalfPlaneModel ∘ (φ'.extend closedUpperHalfPlaneModel).symm) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact memWkpLoc_comp_bordered_transition hφ hφ' zero_le_one hg hW hmaps
  obtain ⟨Φ, hΦω, hsub, hagree⟩ := exists_extension_bordered_transition hφ hφ'
  -- The extension is holomorphic in both directions, hence real `Cᵏ`.
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at hΦω
  simp only [contDiffPregroupoid, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.id_comp, Function.comp_id, preimage_id_eq, id_eq, range_id, inter_univ] at hΦω
  have hΦ : ContDiffOn ℝ k Φ Φ.source := (hΦω.1.restrict_scalars ℝ).of_le le_top
  have hΦ' : ContDiffOn ℝ k Φ.symm Φ.target := (hΦω.2.restrict_scalars ℝ).of_le le_top
  have hk0 : (k : WithTop ℕ∞) ≠ 0 := by exact_mod_cast hk.ne'
  -- Both coordinate domains are half-discs over open sets.
  obtain ⟨Ω, hΩ, hV⟩ := φ.exists_isOpen_extend_target_inter_preimage hT
  obtain ⟨Ω', hΩ', hW'⟩ := φ'.exists_isOpen_extend_target_inter_preimage hT'
  rw [hV] at hg hmaps
  rw [hW'] at hW hmaps ⊢
  let U : Opens ℂ := ⟨Ω' ∩ Φ.source, hΩ'.inter Φ.open_source⟩
  have hUW : (U : Set ℂ) ∩ {z : ℂ | 0 ≤ z.im} = Ω' ∩ {z : ℂ | 0 ≤ z.im} :=
    Subset.antisymm (fun z hz ↦ ⟨hz.1.1, hz.2⟩) fun z hz ↦ ⟨⟨hz.1, hsub (hW hz)⟩, hz.2⟩
  have h := MemWkpLoc.comp_contDiffOn_halfPlane (U := U) (V := ⟨Ω, hΩ⟩) hk hg
    (hΦ.mono inter_subset_right)
    (fun z hz ↦ Φ.det_fderiv_ne_zero_of_contDiffOn hΦ hΦ' hk0 hz.2) fun z hz ↦ by
      rw [hagree z hz.2]
      exact hmaps (hUW ▸ hz)
  rw [hUW] at h
  exact h.congr fun z hz ↦ by simp only [Function.comp_apply, hagree z hz.2]

end Bordered

end TauCeti
