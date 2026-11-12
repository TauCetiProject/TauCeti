/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Sobolev.LocalMap.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import TauCeti.Analysis.Sobolev.Local.ChainRule.Higher
import TauCeti.Analysis.Sobolev.Local.ChangeOfVariables.Higher
import TauCeti.Analysis.Sobolev.Local.Locality
import TauCeti.Geometry.Manifold.Complex.Analytic
import TauCeti.Geometry.Manifold.MFDeriv.ModelChart

/-!
# Chart calculus for local Sobolev maps of every order

Let `X` be a Riemann surface and `M` a smooth manifold without boundary modelled on a
finite-dimensional real normed space, and let `2 < p < ∞`. For every order `k` and open `s`, the
local Sobolev class `TauCeti.MemWkpLocMapOn I p k u s` may be tested in the charts of any
subfamilies of the maximal atlases covering `s` and `u '' s`, and composition with `C^ℓ` maps,
`ℓ ≥ k`, preserves it. The file `TauCeti.Geometry.Manifold.Sobolev.LocalMap.Atlas` proves the same
for `k ≤ 1` and every exponent.

Changing the holomorphic chart is the change of variables `MemWkpLoc.comp_contDiffOn` of every
order along the transition map, which is real `C^k` with invertible derivative. Changing the chart
of `M`, or composing with a `C^ℓ` map, is the chain rule `MemWkpLoc.contDiffOn_comp_succ` for
continuous `W^{k,p}_loc` maps, which needs `p > 2`; continuity is part of the class. The two steps
are glued with the locality of the planar classes, `memWkpLoc_iff_locally`.

## Main declarations

* `TauCeti.memWkpLocMapOn_iff_of_subset_maximalAtlas_of_two_lt`: **chart independence** at every
  order, testing families of charts covering `s` and `u '' s`;
  `TauCeti.memWkpLocMapOn_iff_atlas_of_two_lt` and `TauCeti.memWkpLocMapOn_iff_chartAt_of_two_lt`
  for the atlases and the preferred charts, and the versions for `TauCeti.MemWkpLocMap`.
* `TauCeti.MemWkpLocMapOn.contMDiffOn_comp_of_two_lt`, `ContMDiff.comp_memWkpLocMap_of_two_lt`:
  composition with `C^ℓ` maps, `ℓ ≥ k`, into any manifold modelled on a finite-dimensional real
  normed space.
* `Diffeomorph.memWkpLocMapOn_diffeomorph_comp_iff_of_two_lt`,
  `Diffeomorph.memWkpLocMap_diffeomorph_comp_iff_of_two_lt`: invariance under `C^ℓ`
  diffeomorphisms of the target, `ℓ ≥ k`.

## Implementation notes

As for orders at most one, the target `M` is assumed boundaryless, while the target `N` of a
composition may have corners. The model spaces of `M` and `N` are finite-dimensional because the
planar chain rule and change of variables of every order are proved for finite-dimensional values.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1.
-/

public section

open Set Filter MeasureTheory TopologicalSpace
open scoped Manifold ContDiff Topology NNReal

noncomputable section

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] [FiniteDimensional ℝ F']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ F' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {p : ENNReal} {k : ℕ} {u : X → M} {s : Set X}

/-! ### Auxiliary facts on coordinate expressions -/

omit [ChartedSpace ℂ X] [ChartedSpace H M] [FiniteDimensional ℝ F] in
/-- The coordinate expression of a map continuous on `s` is continuous on its domain. -/
private theorem continuousOn_chart (hu : ContinuousOn u s) (φ : OpenPartialHomeomorph X ℂ)
    (ψ : OpenPartialHomeomorph M H) :
    ContinuousOn (ψ.extend I ∘ u ∘ φ.symm) (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) := by
  refine (ψ.continuousOn_extend).comp (hu.comp (φ.continuousOn_symm.mono inter_subset_left)
    fun _ hz ↦ hz.2.1) fun _ hz ↦ ?_
  simpa using hz.2.2

omit [ChartedSpace ℂ X] [ChartedSpace H M] [FiniteDimensional ℝ F] in
/-- The domain of a coordinate expression of a map continuous on an open set is open. -/
private theorem isOpen_chart (hu : ContinuousOn u s) (hs : IsOpen s)
    (φ : OpenPartialHomeomorph X ℂ) (ψ : OpenPartialHomeomorph M H) :
    IsOpen (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) :=
  φ.isOpen_inter_preimage_symm (hu.isOpen_inter_preimage hs ψ.open_source)

omit [FiniteDimensional ℝ F] in
/-- **Change of holomorphic chart at every order.** For `1 ≤ p < ∞` and `k ≥ 1`, precomposition
with the transition map `φ ∘ φ'⁻¹` between two holomorphic charts preserves the local classes of
order `k` of maps into a finite-dimensional space. -/
private theorem memWkpLoc_comp_chart_transition_of_one_le [Fact (1 ≤ p)] (hp' : p ≠ ⊤)
    (hk : 1 ≤ k) {φ φ' : OpenPartialHomeomorph X ℂ}
    (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X) (hφ' : φ' ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {g : ℂ → E}
    {U W : Set ℂ} (hU : IsOpen U) (hWo : IsOpen W) (hg : MemWkpLoc p U k g)
    (hW : W ⊆ φ'.target ∩ φ'.symm ⁻¹' φ.source) (hmaps : MapsTo (φ ∘ φ'.symm) W U) :
    MemWkpLoc p W k (g ∘ φ ∘ φ'.symm) := by
  have hφR := IsManifold.maximalAtlas_subset_restrictScalars_of_ne_zero 1 one_ne_zero hφ
  have hφ'R := IsManifold.maximalAtlas_subset_restrictScalars_of_ne_zero 1 one_ne_zero hφ'
  have hφRk := IsManifold.maximalAtlas_subset_restrictScalars_of_ne_zero k one_ne_zero hφ
  have hφ'Rk := IsManifold.maximalAtlas_subset_restrictScalars_of_ne_zero k one_ne_zero hφ'
  have hsrc : (φ'.symm.trans φ).source = φ'.target ∩ φ'.symm ⁻¹' φ.source := by
    simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source]
  have hW' : W ⊆ (φ'.symm.trans φ).source := hsrc ▸ hW
  have hΦ : ContDiffOn ℝ k (φ'.symm.trans φ) W := fun z hz ↦
    (contDiffAt_symm_trans_of_mem_maximalAtlas hφ'Rk hφRk (hW' hz)).contDiffWithinAt
  exact hg.comp_contDiffOn (U := ⟨W, hWo⟩) (V := ⟨U, hU⟩) hp' hk hΦ (fun z hz ↦ by
    obtain ⟨A, hA⟩ := exists_hasFDerivAt_symm_trans one_ne_zero hφ'R hφR (hW' hz)
    have hA' : fderiv ℝ (φ ∘ φ'.symm) z = A := hA.fderiv
    rw [hA']
    exact A.toLinearEquiv.isUnit_det'.ne_zero) hmaps

/-- **Change of target chart through a `C^{k+1}` map.** Let `2 < p < ∞`. If `ψ ∘ v` is a
continuous `W^{k+1,p}_loc` map on an open set `W` with `v` mapping `W` into the source of `ψ`, and
`f` is `C^{k+1}` on an open set containing `v '' W`, then `ψ' ∘ f ∘ v` is in `W^{k+1,p}_loc(W)` for
every chart `ψ'` of the target whose source contains `f '' (v '' W)`. -/
private theorem memWkpLoc_extend_comp_of_two_lt [I.Boundaryless] (hp : 2 < p) (hp' : p ≠ ⊤)
    {ψ : OpenPartialHomeomorph M H} (hψ : ψ ∈ IsManifold.maximalAtlas I ∞ M)
    {ψ' : OpenPartialHomeomorph N H'} (hψ' : ψ' ∈ IsManifold.maximalAtlas I' ∞ N)
    {f : M → N} {t : Set M} (hf : ContMDiffOn I I' (k + 1) f t) (ht : IsOpen t)
    {v : ℂ → M} {W : Set ℂ} (hW : IsOpen W) (hv : MemWkpLoc p W (k + 1) (ψ.extend I ∘ v))
    (hvc : ContinuousOn (ψ.extend I ∘ v) W)
    (hmaps : MapsTo v W (ψ.source ∩ (t ∩ f ⁻¹' ψ'.source))) :
    MemWkpLoc p W (k + 1) (ψ'.extend I' ∘ f ∘ v) := by
  lift p to ℝ≥0 using hp'
  have hp2 : 2 < p := by exact_mod_cast hp
  have hO : IsOpen ((ψ.extend I).target ∩ (ψ.extend I).symm ⁻¹' (t ∩ f ⁻¹' ψ'.source)) :=
    ψ.continuousOn_extend_symm.isOpen_inter_preimage ψ.isOpen_extend_target
      (hf.continuousOn.isOpen_inter_preimage ht ψ'.open_source)
  have hle : ((k + 1 : ℕ) : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top
  have hsymm : ContMDiffOn 𝓘(ℝ, F) I (k + 1) (ψ.extend I).symm (ψ.extend I).target := by
    rw [ψ.extend_target']
    exact (contMDiffOn_extend_symm hψ).of_le (by exact_mod_cast hle)
  have hh : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, F') (k + 1) (ψ'.extend I' ∘ f ∘ (ψ.extend I).symm)
      ((ψ.extend I).target ∩ (ψ.extend I).symm ⁻¹' (t ∩ f ⁻¹' ψ'.source)) :=
    ((ψ'.contMDiffOn_extend hψ').of_le (by exact_mod_cast hle)).comp
      (hf.comp (hsymm.mono inter_subset_left) fun _ hy ↦ hy.2.1) fun _ hy ↦ hy.2.2
  have hmaps' : MapsTo (ψ.extend I ∘ v) W
      ((ψ.extend I).target ∩ (ψ.extend I).symm ⁻¹' (t ∩ f ⁻¹' ψ'.source)) := fun w hw ↦ by
    have hvw := hmaps hw
    refine ⟨(ψ.extend I).map_source (by simpa using hvw.1), ?_⟩
    simpa [ψ.left_inv hvw.1] using hvw.2
  refine (MemWkpLoc.contDiffOn_comp_succ (Ω := ⟨W, hW⟩) hp2 hv hvc hO
    (contMDiffOn_iff_contDiffOn.1 hh) hmaps').congr_fun (fun w hw ↦ ?_) hW.measurableSet
  simp [ψ.left_inv (hmaps hw).1]

/-! ### Chart independence -/

section ChartIndependence

variable [I.Boundaryless]

/-- **Chart independence of the local Sobolev class at every order.** For `2 < p < ∞`, every
order `k` and open `s`, it suffices to test the coordinate expressions in the charts of a family
`A` of holomorphic charts covering `s` and a family `B` of smooth charts of `M` covering
`u '' s`. -/
theorem memWkpLocMapOn_iff_of_subset_maximalAtlas_of_two_lt (hp : 2 < p) (hp' : p ≠ ⊤)
    (hs : IsOpen s)
    {A : Set (OpenPartialHomeomorph X ℂ)} (hA : A ⊆ IsManifold.maximalAtlas 𝓘(ℂ) 1 X)
    (hAs : ∀ x ∈ s, ∃ φ ∈ A, x ∈ φ.source)
    {B : Set (OpenPartialHomeomorph M H)} (hB : B ⊆ IsManifold.maximalAtlas I ∞ M)
    (hBs : ∀ x ∈ s, ∃ ψ ∈ B, u x ∈ ψ.source) :
    MemWkpLocMapOn I p k u s ↔ ContinuousOn u s ∧ ∀ φ ∈ A, ∀ ψ ∈ B,
      MemWkpLoc p (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) k (ψ.extend I ∘ u ∘ φ.symm) := by
  refine ⟨fun hu ↦ ⟨hu.continuousOn, fun φ hφ ψ hψ ↦ hu.memWkpLoc_chart (hA hφ) (hB hψ)⟩,
    fun ⟨hc, h⟩ ↦ ?_⟩
  rcases k with _ | k
  · exact memWkpLocMapOn_zero_iff.2 hc
  have : Fact (1 ≤ p) := ⟨one_le_two.trans hp.le⟩
  refine memWkpLocMapOn_iff.2 ⟨hc, fun φ' hφ' ψ' hψ' ↦ ?_⟩
  -- Change the holomorphic chart, for each chart of `B`.
  have h1 : ∀ ψ ∈ B, MemWkpLoc p (φ'.target ∩ φ'.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) (k + 1)
      (ψ.extend I ∘ u ∘ φ'.symm) := by
    intro ψ hψ
    refine memWkpLoc_iff_locally.2 fun z hz ↦ ?_
    obtain ⟨φ, hφA, hxφ⟩ := hAs _ hz.2.1
    have hO : IsOpen (φ'.target ∩ φ'.symm ⁻¹' φ.source) :=
      φ'.isOpen_inter_preimage_symm φ.open_source
    refine ⟨_, inter_mem_nhdsWithin _ (hO.mem_nhds ⟨hz.1, hxφ⟩),
      (memWkpLoc_comp_chart_transition_of_one_le hp' le_add_self (hA hφA) hφ'
        (isOpen_chart hc hs φ ψ) ((isOpen_chart hc hs φ' ψ).inter hO) (h φ hφA ψ hψ)
        inter_subset_right fun w hw ↦ ?_).congr_fun (fun w hw ↦ ?_)
        ((isOpen_chart hc hs φ' ψ).inter hO).measurableSet⟩
    · refine ⟨φ.map_source hw.2.2, ?_⟩
      simpa [Function.comp_apply, φ.left_inv hw.2.2] using hw.1.2
    · simp [φ.left_inv hw.2.2]
  -- Change the chart of `M`.
  refine memWkpLoc_iff_locally.2 fun z hz ↦ ?_
  obtain ⟨ψ, hψB, hxψ⟩ := hBs _ hz.2.1
  have hO := isOpen_chart hc hs φ' ψ
  refine ⟨_, inter_mem_nhdsWithin _ (hO.mem_nhds ⟨hz.1, hz.2.1, hxψ⟩), ?_⟩
  exact memWkpLoc_extend_comp_of_two_lt hp hp' (hB hψB) hψ' contMDiffOn_id isOpen_univ
    ((isOpen_chart hc hs φ' ψ').inter hO) ((h1 ψ hψB).mono inter_subset_right)
    ((continuousOn_chart hc φ' ψ).mono inter_subset_right)
    fun w hw ↦ ⟨hw.2.2.2, mem_univ _, hw.1.2.2⟩

/-- **Chart independence on the whole surface at every order.** For `2 < p < ∞` and every order
`k`, it suffices to test the coordinate expressions in the charts of a family `A` of holomorphic
charts covering `X` and a family `B` of smooth charts covering the image of `u`. -/
theorem memWkpLocMap_iff_of_subset_maximalAtlas_of_two_lt (hp : 2 < p) (hp' : p ≠ ⊤)
    {A : Set (OpenPartialHomeomorph X ℂ)} (hA : A ⊆ IsManifold.maximalAtlas 𝓘(ℂ) 1 X)
    (hAs : ∀ x, ∃ φ ∈ A, x ∈ φ.source)
    {B : Set (OpenPartialHomeomorph M H)} (hB : B ⊆ IsManifold.maximalAtlas I ∞ M)
    (hBs : ∀ x, ∃ ψ ∈ B, u x ∈ ψ.source) :
    MemWkpLocMap I p k u ↔ Continuous u ∧ ∀ φ ∈ A, ∀ ψ ∈ B,
      MemWkpLoc p (φ.target ∩ φ.symm ⁻¹' (u ⁻¹' ψ.source)) k (ψ.extend I ∘ u ∘ φ.symm) := by
  have h : MemWkpLocMapOn I p k u univ ↔ MemWkpLocMap I p k u :=
    memWkpLocMapOnGroupoid_univ
  rw [← h, memWkpLocMapOn_iff_of_subset_maximalAtlas_of_two_lt hp hp' isOpen_univ hA
    (fun x _ ↦ hAs x) hB (fun x _ ↦ hBs x)]
  simp only [continuousOn_univ, univ_inter]

/-- Chart independence at every order: for `2 < p < ∞` and open `s`, it suffices to test the
charts of the atlases of `X` and `M`. -/
theorem memWkpLocMapOn_iff_atlas_of_two_lt [IsManifold 𝓘(ℂ) 1 X] [IsManifold I ∞ M]
    (hp : 2 < p) (hp' : p ≠ ⊤) (hs : IsOpen s) :
    MemWkpLocMapOn I p k u s ↔ ContinuousOn u s ∧ ∀ φ ∈ atlas ℂ X, ∀ ψ ∈ atlas H M,
      MemWkpLoc p (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) k (ψ.extend I ∘ u ∘ φ.symm) :=
  memWkpLocMapOn_iff_of_subset_maximalAtlas_of_two_lt hp hp' hs IsManifold.subset_maximalAtlas
    (fun x _ ↦ ⟨_, chart_mem_atlas ℂ x, mem_chart_source ℂ x⟩) IsManifold.subset_maximalAtlas
    fun x _ ↦ ⟨_, chart_mem_atlas H (u x), mem_chart_source H (u x)⟩

/-- Chart independence at every order: for `2 < p < ∞`, it suffices to test the charts of the
atlases of `X` and `M`. -/
theorem memWkpLocMap_iff_atlas_of_two_lt [IsManifold 𝓘(ℂ) 1 X] [IsManifold I ∞ M]
    (hp : 2 < p) (hp' : p ≠ ⊤) :
    MemWkpLocMap I p k u ↔ Continuous u ∧ ∀ φ ∈ atlas ℂ X, ∀ ψ ∈ atlas H M,
      MemWkpLoc p (φ.target ∩ φ.symm ⁻¹' (u ⁻¹' ψ.source)) k (ψ.extend I ∘ u ∘ φ.symm) :=
  memWkpLocMap_iff_of_subset_maximalAtlas_of_two_lt hp hp' IsManifold.subset_maximalAtlas
    (fun x ↦ ⟨_, chart_mem_atlas ℂ x, mem_chart_source ℂ x⟩) IsManifold.subset_maximalAtlas
    fun x ↦ ⟨_, chart_mem_atlas H (u x), mem_chart_source H (u x)⟩

/-- Chart independence at every order: for `2 < p < ∞` and open `s`, it suffices to test the
preferred charts of `X` and `M`. -/
theorem memWkpLocMapOn_iff_chartAt_of_two_lt [IsManifold 𝓘(ℂ) 1 X] [IsManifold I ∞ M]
    (hp : 2 < p) (hp' : p ≠ ⊤) (hs : IsOpen s) :
    MemWkpLocMapOn I p k u s ↔ ContinuousOn u s ∧ ∀ x : X, ∀ y : M,
      MemWkpLoc p ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' (s ∩ u ⁻¹' (chartAt H y).source))
        k (extChartAt I y ∘ u ∘ (chartAt ℂ x).symm) := by
  rw [memWkpLocMapOn_iff_of_subset_maximalAtlas_of_two_lt hp hp' hs (A := range (chartAt ℂ))
    (range_subset_iff.2 IsManifold.chart_mem_maximalAtlas)
    (fun x _ ↦ ⟨_, mem_range_self x, mem_chart_source ℂ x⟩)
    (B := range (chartAt H)) (range_subset_iff.2 IsManifold.chart_mem_maximalAtlas)
    fun x _ ↦ ⟨_, mem_range_self (u x), mem_chart_source H (u x)⟩]
  simp only [forall_mem_range, extChartAt]

/-- Chart independence at every order: for `2 < p < ∞`, it suffices to test the preferred charts
of `X` and `M`. -/
theorem memWkpLocMap_iff_chartAt_of_two_lt [IsManifold 𝓘(ℂ) 1 X] [IsManifold I ∞ M]
    (hp : 2 < p) (hp' : p ≠ ⊤) :
    MemWkpLocMap I p k u ↔ Continuous u ∧ ∀ x : X, ∀ y : M,
      MemWkpLoc p ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' (u ⁻¹' (chartAt H y).source))
        k (extChartAt I y ∘ u ∘ (chartAt ℂ x).symm) := by
  have h : MemWkpLocMapOn I p k u univ ↔ MemWkpLocMap I p k u :=
    memWkpLocMapOnGroupoid_univ
  rw [← h, memWkpLocMapOn_iff_chartAt_of_two_lt hp hp' isOpen_univ]
  simp only [continuousOn_univ, univ_inter]

end ChartIndependence

/-! ### Composition with differentiable maps -/

section Composition

variable [IsManifold I ∞ M] [I.Boundaryless]

/-- **Composition with `C^ℓ` maps at every order.** Let `2 < p < ∞`. If `u` is a local Sobolev map
of order `k` on an open set `s`, mapping `s` into an open set `t` on which `f : M → N` is `C^ℓ`
with `k ≤ ℓ`, then `f ∘ u` is a local Sobolev map of order `k` on `s`. The manifold `N` may have
corners. -/
theorem MemWkpLocMapOn.contMDiffOn_comp_of_two_lt {n : ℕ∞ω} {f : M → N} {t : Set M}
    (hu : MemWkpLocMapOn I p k u s) (hp : 2 < p) (hp' : p ≠ ⊤) (hf : ContMDiffOn I I' n f t)
    (hkn : (k : ℕ∞ω) ≤ n) (hs : IsOpen s) (ht : IsOpen t) (hst : MapsTo u s t) :
    MemWkpLocMapOn I' p k (f ∘ u) s := by
  have hc : ContinuousOn (f ∘ u) s := hf.continuousOn.comp hu.continuousOn hst
  rcases k with _ | k
  · exact memWkpLocMapOn_zero_iff.2 hc
  refine memWkpLocMapOn_iff.2 ⟨hc, fun φ hφ ψ' hψ' ↦ memWkpLoc_iff_locally.2 fun z hz ↦ ?_⟩
  have hO := isOpen_chart hu.continuousOn hs φ (chartAt H (u (φ.symm z)))
  refine ⟨_, inter_mem_nhdsWithin _ (hO.mem_nhds ⟨hz.1, hz.2.1, mem_chart_source _ _⟩), ?_⟩
  exact memWkpLoc_extend_comp_of_two_lt hp hp' (IsManifold.chart_mem_maximalAtlas _) hψ'
    (hf.of_le (by exact_mod_cast hkn)) ht ((isOpen_chart hc hs φ ψ').inter hO)
    ((hu.memWkpLoc_chart hφ (IsManifold.chart_mem_maximalAtlas _)).mono inter_subset_right)
    ((continuousOn_chart hu.continuousOn φ _).mono inter_subset_right)
    fun w hw ↦ ⟨hw.2.2.2, hst hw.2.2.1, hw.1.2.2⟩

/-- **Composition with `C^ℓ` maps at every order.** Let `2 < p < ∞`. If `u` is a local Sobolev map
of order `k` and `f : M → N` is `C^ℓ` with `k ≤ ℓ`, then `f ∘ u` is a local Sobolev map of order
`k`. -/
theorem _root_.ContMDiff.comp_memWkpLocMap_of_two_lt {n : ℕ∞ω} {f : M → N}
    (hf : ContMDiff I I' n f) (hu : MemWkpLocMap I p k u) (hp : 2 < p) (hp' : p ≠ ⊤)
    (hkn : (k : ℕ∞ω) ≤ n) : MemWkpLocMap I' p k (f ∘ u) :=
  memWkpLocMapOnGroupoid_univ.mp (MemWkpLocMapOn.contMDiffOn_comp_of_two_lt
    (memWkpLocMapOnGroupoid_univ.mpr hu) hp hp' hf.contMDiffOn hkn
    isOpen_univ isOpen_univ (mapsTo_univ _ _))

variable [IsManifold I' ∞ N] [I'.Boundaryless]

/-- Composition with a `C^ℓ` diffeomorphism, `ℓ ≥ k`, preserves and reflects the local Sobolev
classes of every order `k` on open sets, for `2 < p < ∞`. -/
theorem _root_.Diffeomorph.memWkpLocMapOn_diffeomorph_comp_iff_of_two_lt {n : ℕ∞ω}
    (e : M ≃ₘ^n⟮I, I'⟯ N) (hp : 2 < p) (hp' : p ≠ ⊤) (hkn : (k : ℕ∞ω) ≤ n) (hs : IsOpen s) :
    MemWkpLocMapOn I' p k (e ∘ u) s ↔ MemWkpLocMapOn I p k u s := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.contMDiffOn_comp_of_two_lt hp hp' e.contMDiff.contMDiffOn hkn hs
    isOpen_univ (mapsTo_univ _ _)⟩
  have := h.contMDiffOn_comp_of_two_lt hp hp' e.symm.contMDiff.contMDiffOn hkn hs isOpen_univ
    (mapsTo_univ _ _)
  simpa [Function.comp_def] using this

/-- Composition with a `C^ℓ` diffeomorphism, `ℓ ≥ k`, preserves and reflects the local Sobolev
classes of every order `k`, for `2 < p < ∞`. -/
theorem _root_.Diffeomorph.memWkpLocMap_diffeomorph_comp_iff_of_two_lt {n : ℕ∞ω}
    (e : M ≃ₘ^n⟮I, I'⟯ N) (hp : 2 < p) (hp' : p ≠ ⊤) (hkn : (k : ℕ∞ω) ≤ n) :
    MemWkpLocMap I' p k (e ∘ u) ↔ MemWkpLocMap I p k u := by
  have h : MemWkpLocMapOn I p k u univ ↔ MemWkpLocMap I p k u :=
    memWkpLocMapOnGroupoid_univ
  have h' : MemWkpLocMapOn I' p k (e ∘ u) univ ↔ MemWkpLocMap I' p k (e ∘ u) :=
    memWkpLocMapOnGroupoid_univ
  rw [← h', ← h, e.memWkpLocMapOn_diffeomorph_comp_iff_of_two_lt hp hp' hkn isOpen_univ]

end Composition

end TauCeti
