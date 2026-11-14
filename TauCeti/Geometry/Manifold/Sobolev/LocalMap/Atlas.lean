/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import TauCeti.Analysis.Sobolev.Local.ChangeOfVariables
public import TauCeti.Geometry.Manifold.Sobolev.LocalMap
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import TauCeti.Analysis.Complex.RealDeriv
import TauCeti.Analysis.Sobolev.Local.ChainRule
import TauCeti.Analysis.Sobolev.Local.Locality
import TauCeti.Geometry.Manifold.Complex.Analytic
import TauCeti.Geometry.Manifold.ExtChartAt
import TauCeti.Geometry.Manifold.MFDeriv.ModelChart

/-!
# Chart calculus for local Sobolev maps of order at most one

Let `X` be a Riemann surface and `M` a smooth manifold without boundary modelled on a real Banach
space. The local Sobolev class `TauCeti.MemWkpLocMapOn I p k u s` tests the coordinate expressions
of `u : X → M` in all charts of the maximal atlases. For `k ≤ 1` and open `s` we show that it
suffices to test the charts of any subfamilies of the maximal atlases covering `s` and `u '' s`,
and that composition with `C^ℓ` maps, `ℓ ≥ k`, preserves the class. Composition is treated for
the classes `TauCeti.MemWkpLocMapOnGroupoid` of any structure groupoid, so it also applies up to
the boundary of a bordered surface.

Changing the holomorphic chart is the change of variables `MemWkpLoc.comp_contDiffOn_diffeo`
along the transition map, which is real `C¹` with invertible derivative. Changing the chart of
`M`, or composing with a `C^ℓ` map, is the chain rule `MemWkpLoc.contDiffOn_comp` for continuous
`W^{1,p}_loc` maps. The two steps are glued with the locality of the planar classes,
`memWkpLoc_iff_locally`. At order zero the class consists of the continuous maps
(`TauCeti.memWkpLocMapOnGroupoid_zero_iff`).

## Main declarations

* `TauCeti.memWkpLoc_comp_chart_transition`: precomposition with the transition map between two
  holomorphic charts preserves the planar classes of order at most one.
* `TauCeti.memWkpLoc_extend_comp`: changing the target chart through a `C¹` map preserves the
  planar class of order one on a measurable set.
* `TauCeti.memWkpLocMapOn_iff_of_subset_maximalAtlas`: **chart independence**, testing families of
  charts covering `s` and `u '' s`; `TauCeti.memWkpLocMapOn_iff_atlas` and
  `TauCeti.memWkpLocMapOn_iff_chartAt` for the atlases and the preferred charts, and the versions
  for `TauCeti.MemWkpLocMap`.
* `TauCeti.MemWkpLocMapOnGroupoid.contMDiffOn_comp`, `ContMDiff.comp_memWkpLocMapGroupoid`:
  composition with `C^ℓ` maps into any manifold modelled on a real Banach space, for the classes
  of any structure groupoid, in particular also up to the boundary of a bordered surface.
* `Diffeomorph.memWkpLocMapOnGroupoid_diffeomorph_comp_iff`,
  `Diffeomorph.memWkpLocMapGroupoid_diffeomorph_comp_iff`: invariance under diffeomorphisms of the
  target.
* `TauCeti.memWkpLoc_mulLeft_two_chart_iff`: on `X = ℂ` the charts `z` and `2 z` give the same
  coordinate tests at every order, with first derivatives scaled by `2`
  (`TauCeti.HasWeakFDerivOn.comp_two_mul`); `TauCeti.conj_chart_notMem_maximalAtlas`: the
  conjugation chart is not a holomorphic chart.

## Implementation notes

The target `M` is assumed boundaryless: for a model with corners the transition maps of `M` are
`C¹` only within the range of the model, while the chain rule for `MemWkpLoc` composes with maps
that are `C¹` on an open set. The target `N` of a composition may have corners. Orders `k ≥ 2`
need the higher-order chain rule and change of variables for planar classes and are not treated.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1.
-/

public section

open Set Filter MeasureTheory TopologicalSpace
open scoped Manifold ContDiff Topology ComplexConjugate

noncomputable section

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ F' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {p : ENNReal} {k : ℕ} {u : X → M} {s : Set X}

/-! ### Auxiliary facts on coordinate expressions -/

omit [ChartedSpace ℂ X] [ChartedSpace H M] in
/-- The domain of a coordinate expression of a map continuous on an open set is open. -/
private theorem isOpen_chart (hu : ContinuousOn u s) (hs : IsOpen s)
    (φ : OpenPartialHomeomorph X ℂ) (ψ : OpenPartialHomeomorph M H) :
    IsOpen (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) :=
  φ.isOpen_inter_preimage_symm (hu.isOpen_inter_preimage hs ψ.open_source)

/-- **Change of holomorphic chart.** Precomposition with the transition map `φ ∘ φ'⁻¹` between
two holomorphic charts preserves the local classes of order at most one. -/
theorem memWkpLoc_comp_chart_transition {φ φ' : OpenPartialHomeomorph X ℂ}
    (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X) (hφ' : φ' ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : ℂ → E} {U W : Set ℂ} (hk : k ≤ 1)
    (hg : MemWkpLoc p U k g) (hW : W ⊆ φ'.target ∩ φ'.symm ⁻¹' φ.source)
    (hmaps : MapsTo (φ ∘ φ'.symm) W U) : MemWkpLoc p W k (g ∘ φ ∘ φ'.symm) := by
  have hφR := IsManifold.maximalAtlas_subset_restrictScalars_of_ne_zero 1 one_ne_zero hφ
  have hφ'R := IsManifold.maximalAtlas_subset_restrictScalars_of_ne_zero 1 one_ne_zero hφ'
  have hsrc : (φ'.symm.trans φ).source = φ'.target ∩ φ'.symm ⁻¹' φ.source := by
    simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source]
  have hW' : W ⊆ (φ'.symm.trans φ).source := hsrc ▸ hW
  have hΦ : ContDiffOn ℝ 1 (φ'.symm.trans φ) (φ'.symm.trans φ).source := fun z hz ↦
    (contDiffAt_symm_trans_of_mem_maximalAtlas hφ'R hφR hz).contDiffWithinAt
  refine hg.comp_contDiffOn_diffeo (Φ := φ'.symm.trans φ) hk (φ'.symm.trans φ).open_source hΦ
    ((φ'.symm.trans φ).injOn.mono hW') (fun z hz ↦ ?_) hW' hmaps
  obtain ⟨A, hA⟩ := exists_hasFDerivAt_symm_trans one_ne_zero hφ'R hφR (hW' hz)
  rw [hA.fderiv]
  exact A.toLinearEquiv.isUnit_det'.ne_zero

/-- **Change of target chart through a `C¹` map.** If `ψ ∘ v` is a continuous `W^{1,p}_loc` map on
a set `W` with `v` mapping `W` into the source of `ψ`, and `f` is `C¹` on an open set
containing `v '' W`, then `ψ' ∘ f ∘ v` is in `W^{1,p}_loc(W)` for every chart `ψ'` of the target
whose source contains `f '' (v '' W)`. -/
theorem memWkpLoc_extend_comp [I.Boundaryless] [CompleteSpace F']
    {ψ : OpenPartialHomeomorph M H} (hψ : ψ ∈ IsManifold.maximalAtlas I ∞ M)
    {ψ' : OpenPartialHomeomorph N H'} (hψ' : ψ' ∈ IsManifold.maximalAtlas I' ∞ N)
    {f : M → N} {t : Set M} (hf : ContMDiffOn I I' 1 f t) (ht : IsOpen t)
    {v : ℂ → M} {W : Set ℂ} (hv : MemWkpLoc p W 1 (ψ.extend I ∘ v))
    (hvc : ContinuousOn (ψ.extend I ∘ v) W)
    (hmaps : MapsTo v W (ψ.source ∩ (t ∩ f ⁻¹' ψ'.source))) :
    MemWkpLoc p W 1 (ψ'.extend I' ∘ f ∘ v) := by
  have hO : IsOpen ((ψ.extend I).target ∩ (ψ.extend I).symm ⁻¹' (t ∩ f ⁻¹' ψ'.source)) :=
    ψ.continuousOn_extend_symm.isOpen_inter_preimage ψ.isOpen_extend_target
      (hf.continuousOn.isOpen_inter_preimage ht ψ'.open_source)
  have hsymm : ContMDiffOn 𝓘(ℝ, F) I 1 (ψ.extend I).symm (ψ.extend I).target := by
    rw [ψ.extend_target']
    exact (contMDiffOn_extend_symm hψ).of_le (by exact_mod_cast le_top)
  have hh : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, F') 1 (ψ'.extend I' ∘ f ∘ (ψ.extend I).symm)
      ((ψ.extend I).target ∩ (ψ.extend I).symm ⁻¹' (t ∩ f ⁻¹' ψ'.source)) :=
    ((ψ'.contMDiffOn_extend hψ').of_le (by exact_mod_cast le_top)).comp
      (hf.comp (hsymm.mono inter_subset_left) fun _ hy ↦ hy.2.1) fun _ hy ↦ hy.2.2
  have hmaps' : MapsTo (ψ.extend I ∘ v) W
      ((ψ.extend I).target ∩ (ψ.extend I).symm ⁻¹' (t ∩ f ⁻¹' ψ'.source)) := fun w hw ↦ by
    have hvw := hmaps hw
    refine ⟨(ψ.extend I).map_source (by simpa using hvw.1), ?_⟩
    simpa [ψ.left_inv hvw.1] using hvw.2
  refine (hv.contDiffOn_comp hvc hO (contMDiffOn_iff_contDiffOn.1 hh) hmaps').congr
    fun w hw ↦ ?_
  simp [ψ.left_inv (hmaps hw).1]

/-! ### Chart independence -/

section ChartIndependence

variable [I.Boundaryless] [CompleteSpace F]

/-- **Chart independence of the local Sobolev class.** For `k ≤ 1` and open `s`, it suffices to
test the coordinate expressions in the charts of a family `A` of holomorphic charts covering `s`
and a family `B` of smooth charts of `M` covering `u '' s`. -/
theorem memWkpLocMapOn_iff_of_subset_maximalAtlas (hk : k ≤ 1) (hs : IsOpen s)
    {A : Set (OpenPartialHomeomorph X ℂ)} (hA : A ⊆ IsManifold.maximalAtlas 𝓘(ℂ) 1 X)
    (hAs : ∀ x ∈ s, ∃ φ ∈ A, x ∈ φ.source)
    {B : Set (OpenPartialHomeomorph M H)} (hB : B ⊆ IsManifold.maximalAtlas I ∞ M)
    (hBs : ∀ x ∈ s, ∃ ψ ∈ B, u x ∈ ψ.source) :
    MemWkpLocMapOn I p k u s ↔ ContinuousOn u s ∧ ∀ φ ∈ A, ∀ ψ ∈ B,
      MemWkpLoc p (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) k (ψ.extend I ∘ u ∘ φ.symm) := by
  refine ⟨fun hu ↦ ⟨hu.continuousOn, fun φ hφ ψ hψ ↦ hu.memWkpLoc_chart (hA hφ) (hB hψ)⟩,
    fun ⟨hc, h⟩ ↦ ?_⟩
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hk with rfl | rfl
  · exact memWkpLocMapOnGroupoid_zero_iff.2 hc
  refine memWkpLocMapOn_iff.2 ⟨hc, fun φ' hφ' ψ' hψ' ↦ ?_⟩
  -- Change the holomorphic chart, for each chart of `B`.
  have h1 : ∀ ψ ∈ B, MemWkpLoc p (φ'.target ∩ φ'.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) 1
      (ψ.extend I ∘ u ∘ φ'.symm) := by
    intro ψ hψ
    refine memWkpLoc_iff_locally.2 fun z hz ↦ ?_
    obtain ⟨φ, hφA, hxφ⟩ := hAs _ hz.2.1
    have hO : IsOpen (φ'.target ∩ φ'.symm ⁻¹' φ.source) :=
      φ'.isOpen_inter_preimage_symm φ.open_source
    refine ⟨_, inter_mem_nhdsWithin _ (hO.mem_nhds ⟨hz.1, hxφ⟩),
      (memWkpLoc_comp_chart_transition (hA hφA) hφ' le_rfl (h φ hφA ψ hψ) inter_subset_right
        fun w hw ↦ ?_).congr fun w hw ↦ ?_⟩
    · refine ⟨φ.map_source hw.2.2, ?_⟩
      simpa [Function.comp_apply, φ.left_inv hw.2.2] using hw.1.2
    · simp [φ.left_inv hw.2.2]
  -- Change the chart of `M`.
  refine memWkpLoc_iff_locally.2 fun z hz ↦ ?_
  obtain ⟨ψ, hψB, hxψ⟩ := hBs _ hz.2.1
  have hO := isOpen_chart hc hs φ' ψ
  refine ⟨_, inter_mem_nhdsWithin _ (hO.mem_nhds ⟨hz.1, hz.2.1, hxψ⟩), ?_⟩
  have hcψ : ContinuousOn (ψ.extend I ∘ u ∘ φ'.symm)
      (φ'.target ∩ φ'.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) := by
    simpa only [mfld_simps] using hc.extend_comp_extend_symm (J := 𝓘(ℝ, ℂ)) φ' ψ
  exact memWkpLoc_extend_comp (hB hψB) hψ' contMDiffOn_id isOpen_univ
    ((h1 ψ hψB).mono inter_subset_right)
    (hcψ.mono inter_subset_right) fun w hw ↦ ⟨hw.2.2.2, mem_univ _, hw.1.2.2⟩

/-- **Chart independence on the whole surface.** For `k ≤ 1`, it suffices to test the coordinate
expressions in the charts of a family `A` of holomorphic charts covering `X` and a family `B` of
smooth charts covering the image of `u`. -/
theorem memWkpLocMap_iff_of_subset_maximalAtlas (hk : k ≤ 1)
    {A : Set (OpenPartialHomeomorph X ℂ)} (hA : A ⊆ IsManifold.maximalAtlas 𝓘(ℂ) 1 X)
    (hAs : ∀ x, ∃ φ ∈ A, x ∈ φ.source)
    {B : Set (OpenPartialHomeomorph M H)} (hB : B ⊆ IsManifold.maximalAtlas I ∞ M)
    (hBs : ∀ x, ∃ ψ ∈ B, u x ∈ ψ.source) :
    MemWkpLocMap I p k u ↔ Continuous u ∧ ∀ φ ∈ A, ∀ ψ ∈ B,
      MemWkpLoc p (φ.target ∩ φ.symm ⁻¹' (u ⁻¹' ψ.source)) k (ψ.extend I ∘ u ∘ φ.symm) := by
  have h : MemWkpLocMapOn I p k u univ ↔ MemWkpLocMap I p k u :=
    memWkpLocMapOnGroupoid_univ
  rw [← h, memWkpLocMapOn_iff_of_subset_maximalAtlas hk isOpen_univ hA
    (fun x _ ↦ hAs x) hB (fun x _ ↦ hBs x)]
  simp only [continuousOn_univ, univ_inter]

/-- Chart independence: for `k ≤ 1` and open `s`, it suffices to test the charts of the atlases
of `X` and `M`. -/
theorem memWkpLocMapOn_iff_atlas [IsManifold 𝓘(ℂ) 1 X] [IsManifold I ∞ M] (hk : k ≤ 1)
    (hs : IsOpen s) :
    MemWkpLocMapOn I p k u s ↔ ContinuousOn u s ∧ ∀ φ ∈ atlas ℂ X, ∀ ψ ∈ atlas H M,
      MemWkpLoc p (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) k (ψ.extend I ∘ u ∘ φ.symm) :=
  memWkpLocMapOn_iff_of_subset_maximalAtlas hk hs IsManifold.subset_maximalAtlas
    (fun x _ ↦ ⟨_, chart_mem_atlas ℂ x, mem_chart_source ℂ x⟩) IsManifold.subset_maximalAtlas
    fun x _ ↦ ⟨_, chart_mem_atlas H (u x), mem_chart_source H (u x)⟩

/-- Chart independence: for `k ≤ 1`, it suffices to test the charts of the atlases of `X` and
`M`. -/
theorem memWkpLocMap_iff_atlas [IsManifold 𝓘(ℂ) 1 X] [IsManifold I ∞ M] (hk : k ≤ 1) :
    MemWkpLocMap I p k u ↔ Continuous u ∧ ∀ φ ∈ atlas ℂ X, ∀ ψ ∈ atlas H M,
      MemWkpLoc p (φ.target ∩ φ.symm ⁻¹' (u ⁻¹' ψ.source)) k (ψ.extend I ∘ u ∘ φ.symm) :=
  memWkpLocMap_iff_of_subset_maximalAtlas hk IsManifold.subset_maximalAtlas
    (fun x ↦ ⟨_, chart_mem_atlas ℂ x, mem_chart_source ℂ x⟩) IsManifold.subset_maximalAtlas
    fun x ↦ ⟨_, chart_mem_atlas H (u x), mem_chart_source H (u x)⟩

/-- Chart independence: for `k ≤ 1` and open `s`, it suffices to test the preferred charts of `X`
and `M`. -/
theorem memWkpLocMapOn_iff_chartAt [IsManifold 𝓘(ℂ) 1 X] [IsManifold I ∞ M] (hk : k ≤ 1)
    (hs : IsOpen s) :
    MemWkpLocMapOn I p k u s ↔ ContinuousOn u s ∧ ∀ x : X, ∀ y : M,
      MemWkpLoc p ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' (s ∩ u ⁻¹' (chartAt H y).source))
        k (extChartAt I y ∘ u ∘ (chartAt ℂ x).symm) := by
  rw [memWkpLocMapOn_iff_of_subset_maximalAtlas hk hs (A := range (chartAt ℂ))
    (range_subset_iff.2 IsManifold.chart_mem_maximalAtlas)
    (fun x _ ↦ ⟨_, mem_range_self x, mem_chart_source ℂ x⟩)
    (B := range (chartAt H)) (range_subset_iff.2 IsManifold.chart_mem_maximalAtlas)
    fun x _ ↦ ⟨_, mem_range_self (u x), mem_chart_source H (u x)⟩]
  simp only [forall_mem_range, extChartAt]

/-- Chart independence: for `k ≤ 1`, it suffices to test the preferred charts of `X` and `M`. -/
theorem memWkpLocMap_iff_chartAt [IsManifold 𝓘(ℂ) 1 X] [IsManifold I ∞ M] (hk : k ≤ 1) :
    MemWkpLocMap I p k u ↔ Continuous u ∧ ∀ x : X, ∀ y : M,
      MemWkpLoc p ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' (u ⁻¹' (chartAt H y).source))
        k (extChartAt I y ∘ u ∘ (chartAt ℂ x).symm) := by
  have h : MemWkpLocMapOn I p k u univ ↔ MemWkpLocMap I p k u :=
    memWkpLocMapOnGroupoid_univ
  rw [← h, memWkpLocMapOn_iff_chartAt hk isOpen_univ]
  simp only [continuousOn_univ, univ_inter]

end ChartIndependence

/-! ### Composition with differentiable maps -/

section Composition

variable {H₀ : Type*} [TopologicalSpace H₀] {Y : Type*} [TopologicalSpace Y] [ChartedSpace H₀ Y]
  {G : StructureGroupoid H₀} {J : ModelWithCorners ℝ ℂ H₀} {v : Y → M} {S : Set Y}
  [IsManifold I ∞ M] [I.Boundaryless] [CompleteSpace F']

/-- **Composition with `C^ℓ` maps.** If `v` is a local Sobolev map of order `k ≤ 1` on an open set
`S`, for the charts of any structure groupoid, mapping `S` into an open set `t` on which
`f : M → N` is `C^ℓ` with `k ≤ ℓ`, then `f ∘ v` is a local Sobolev map of order `k` on `S`. The
manifold `N` may have corners. -/
theorem MemWkpLocMapOnGroupoid.contMDiffOn_comp {n : ℕ∞ω} {f : M → N} {t : Set M}
    (hv : MemWkpLocMapOnGroupoid G J I p k v S) (hk : k ≤ 1) (hf : ContMDiffOn I I' n f t)
    (hkn : (k : ℕ∞ω) ≤ n) (hS : IsOpen S) (ht : IsOpen t) (hSt : MapsTo v S t) :
    MemWkpLocMapOnGroupoid G J I' p k (f ∘ v) S := by
  have hc : ContinuousOn (f ∘ v) S := hf.continuousOn.comp hv.continuousOn hSt
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hk with rfl | rfl
  · exact memWkpLocMapOnGroupoid_zero_iff.2 hc
  refine memWkpLocMapOnGroupoid_iff.2
    ⟨hc, fun φ hφ ψ' hψ' ↦ memWkpLoc_iff_locally.2 fun z hz ↦ ?_⟩
  set ψ := chartAt H (v ((φ.extend J).symm z))
  have hO : IsOpen (S ∩ v ⁻¹' ψ.source) := hv.continuousOn.isOpen_inter_preimage hS ψ.open_source
  refine ⟨_, inter_mem self_mem_nhdsWithin (nhdsWithin_mono _
    (inter_subset_left.trans φ.extend_target_subset_range)
    (φ.extend_target_inter_preimage_mem_nhdsWithin hO ⟨hz.1, hz.2.1, mem_chart_source _ _⟩)), ?_⟩
  exact memWkpLoc_extend_comp (IsManifold.chart_mem_maximalAtlas _) hψ' (hf.of_le hkn) ht
    ((hv.memWkpLoc_chart hφ (IsManifold.chart_mem_maximalAtlas _)).mono inter_subset_right)
    ((hv.continuousOn.extend_comp_extend_symm φ ψ).mono inter_subset_right)
    fun w hw ↦ ⟨hw.2.2.2, hSt hw.2.2.1, hw.1.2.2⟩

/-- **Composition with `C^ℓ` maps.** If `v` is a local Sobolev map of order `k ≤ 1`, for the
charts of any structure groupoid, and `f : M → N` is `C^ℓ` with `k ≤ ℓ`, then `f ∘ v` is a local
Sobolev map of order `k`. -/
theorem _root_.ContMDiff.comp_memWkpLocMapGroupoid {n : ℕ∞ω} {f : M → N}
    (hf : ContMDiff I I' n f) (hv : MemWkpLocMapGroupoid G J I p k v) (hk : k ≤ 1)
    (hkn : (k : ℕ∞ω) ≤ n) : MemWkpLocMapGroupoid G J I' p k (f ∘ v) :=
  memWkpLocMapOnGroupoid_univ.mp ((memWkpLocMapOnGroupoid_univ.mpr hv).contMDiffOn_comp hk
    hf.contMDiffOn hkn isOpen_univ isOpen_univ (mapsTo_univ _ _))

variable [IsManifold I' ∞ N] [I'.Boundaryless] [CompleteSpace F]

/-- Composition with a `C^ℓ` diffeomorphism, `ℓ ≥ k`, preserves and reflects the local Sobolev
classes of order `k ≤ 1` on open sets, for the charts of any structure groupoid. -/
theorem _root_.Diffeomorph.memWkpLocMapOnGroupoid_diffeomorph_comp_iff {n : ℕ∞ω}
    (e : M ≃ₘ^n⟮I, I'⟯ N) (hk : k ≤ 1) (hkn : (k : ℕ∞ω) ≤ n) (hS : IsOpen S) :
    MemWkpLocMapOnGroupoid G J I' p k (e ∘ v) S ↔ MemWkpLocMapOnGroupoid G J I p k v S := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.contMDiffOn_comp hk e.contMDiff.contMDiffOn hkn hS isOpen_univ
    (mapsTo_univ _ _)⟩
  have := h.contMDiffOn_comp hk e.symm.contMDiff.contMDiffOn hkn hS isOpen_univ (mapsTo_univ _ _)
  simpa [Function.comp_def] using this

/-- Composition with a `C^ℓ` diffeomorphism, `ℓ ≥ k`, preserves and reflects the local Sobolev
classes of order `k ≤ 1`, for the charts of any structure groupoid. -/
theorem _root_.Diffeomorph.memWkpLocMapGroupoid_diffeomorph_comp_iff {n : ℕ∞ω}
    (e : M ≃ₘ^n⟮I, I'⟯ N) (hk : k ≤ 1) (hkn : (k : ℕ∞ω) ≤ n) :
    MemWkpLocMapGroupoid G J I' p k (e ∘ v) ↔ MemWkpLocMapGroupoid G J I p k v := by
  rw [← memWkpLocMapOnGroupoid_univ, ← memWkpLocMapOnGroupoid_univ,
    e.memWkpLocMapOnGroupoid_diffeomorph_comp_iff hk hkn isOpen_univ]

end Composition

/-! ### Checks on the plane -/

section Checks

/-- The chart `z ↦ 2 z` of `ℂ` is a holomorphic chart. -/
theorem mulLeft_two_chart_mem_maximalAtlas :
    (Homeomorph.mulLeft₀ (2 : ℂ) two_ne_zero).toOpenPartialHomeomorph ∈
      IsManifold.maximalAtlas 𝓘(ℂ) 1 ℂ := by
  refine OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn _ ?_ ?_ <;>
  · rw [contMDiffOn_iff_contDiffOn]
    exact (contDiff_const.mul contDiff_id).contDiffOn

omit [ChartedSpace H M] in
/-- **The charts `z` and `2 z` give the same coordinate tests.** For `v : ℂ → M`, every order `k`
and every chart `ψ` of `M`, the coordinate expression of `v` on `S` in the chart `z ↦ 2 z` is in the
planar class `MemWkpLoc p _ k` exactly when the coordinate expression in the identity chart is. -/
theorem memWkpLoc_mulLeft_two_chart_iff {v : ℂ → M} {S : Set ℂ} (ψ : OpenPartialHomeomorph M H) :
    MemWkpLoc p ((Homeomorph.mulLeft₀ (2 : ℂ) two_ne_zero).toOpenPartialHomeomorph.target ∩
        (Homeomorph.mulLeft₀ (2 : ℂ) two_ne_zero).toOpenPartialHomeomorph.symm ⁻¹'
          (S ∩ v ⁻¹' ψ.source)) k
      (ψ.extend I ∘ v ∘ (Homeomorph.mulLeft₀ (2 : ℂ) two_ne_zero).toOpenPartialHomeomorph.symm) ↔
    MemWkpLoc p ((OpenPartialHomeomorph.refl ℂ).target ∩ (OpenPartialHomeomorph.refl ℂ).symm ⁻¹'
        (S ∩ v ⁻¹' ψ.source)) k (ψ.extend I ∘ v ∘ (OpenPartialHomeomorph.refl ℂ).symm) := by
  set A : ℂ ≃L[ℝ] ℂ := (LinearEquiv.smulOfNeZero ℝ ℂ 2 two_ne_zero).toContinuousLinearEquiv
  have hA : ∀ z, A z = 2 * z := fun z ↦ by simp [A, Complex.real_smul]
  have hAs : ∀ z, A.symm z = 2⁻¹ * z := fun z ↦ by
    rw [A.symm_apply_eq, hA, mul_inv_cancel_left₀ two_ne_zero]
  simp only [mfld_simps, Homeomorph.mulLeft₀_symm_apply]
  constructor
  · intro h
    simpa [Function.comp_def, hA, ← mul_assoc] using
      h.comp_continuousLinearEquiv_add A 0 (U := S ∩ v ⁻¹' ψ.source) fun z hz ↦ by
        simpa [hA, ← mul_assoc] using hz
  · intro h
    simpa [Function.comp_def, hAs] using
      h.comp_continuousLinearEquiv_add A.symm 0 fun z hz ↦ by simpa [hAs] using hz

/-- The conjugation chart `z ↦ conj z` of `ℂ` is not a holomorphic chart, so it is never tested
in the definition of the local Sobolev class. -/
theorem conj_chart_notMem_maximalAtlas :
    Complex.conjCLE.toHomeomorph.toOpenPartialHomeomorph ∉ IsManifold.maximalAtlas 𝓘(ℂ) 1 ℂ := by
  intro h
  have hd := contMDiffOn_of_mem_maximalAtlas h
  rw [Homeomorph.toOpenPartialHomeomorph_source, contMDiffOn_univ, contMDiff_iff_contDiff] at hd
  exact Complex.not_differentiableAt_conj 0 ((hd.differentiable one_ne_zero) 0)

end Checks

end TauCeti
