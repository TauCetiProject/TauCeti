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
import TauCeti.Geometry.Manifold.MFDeriv.ModelChart
import TauCeti.Topology.OpenPartialHomeomorph.Continuity

/-!
# Chart calculus for local Sobolev maps of order at most one

Let `X` be a Riemann surface and `M` a smooth manifold without boundary modelled on a real Banach
space. The local Sobolev class `TauCeti.MemWkpLocMapOn I p k u s` tests the coordinate expressions
of `u : X → M` in all charts of the maximal atlases. For `k ≤ 1` and open `s` we show that it
suffices to test the charts of any subfamilies of the maximal atlases covering `s` and `u '' s`,
and that composition with `C^ℓ` maps, `ℓ ≥ k`, preserves the class.

Changing the holomorphic chart is the change of variables `MemWkpLoc.comp_contDiffOn_diffeo`
along the transition map, which is real `C¹` with invertible derivative. Changing the chart of
`M`, or composing with a `C^ℓ` map, is the chain rule `MemWkpLoc.contDiffOn_comp` for continuous
`W^{1,p}_loc` maps. The two steps are glued with the locality of the planar classes,
`memWkpLoc_iff_locally`. At order zero the class consists of the continuous maps.

## Main declarations

* `TauCeti.memWkpLocMapOn_zero_iff`, `TauCeti.memWkpLocMap_zero_iff`: at order zero the class is
  that of continuous maps.
* `TauCeti.memWkpLocMapOn_iff_of_subset_maximalAtlas`: **chart independence**, testing families of
  charts covering `s` and `u '' s`; `TauCeti.memWkpLocMapOn_iff_atlas` and
  `TauCeti.memWkpLocMapOn_iff_chartAt` for the atlases and the preferred charts, and the versions
  for `TauCeti.MemWkpLocMap`.
* `TauCeti.MemWkpLocMapOn.contMDiffOn_comp`, `ContMDiff.comp_memWkpLocMap`: composition with
  `C^ℓ` maps into any manifold modelled on a real Banach space.
* `Diffeomorph.memWkpLocMapOn_diffeomorph_comp_iff`,
  `Diffeomorph.memWkpLocMap_diffeomorph_comp_iff`: invariance under diffeomorphisms of the target.
* `TauCeti.memWkpLoc_mulLeft_two_chart_iff`: on `X = ℂ` the charts `z` and `2 z` give the same
  coordinate tests at every order, with first derivatives scaled by `2`
  (`TauCeti.HasWeakFDerivOn.comp_two_mul`); `TauCeti.conj_chart_notMem_maximalAtlas`: the
  conjugation chart is not a holomorphic chart.

## Implementation notes

The target `M` is assumed boundaryless: for a model with corners the transition maps of `M` are
`C¹` only within the range of the model, while the chain rule for `MemWkpLoc` composes with maps
that are `C¹` on an open set. The target `N` of a composition may have corners. The gluing proofs
take the planar change of variables and chain rule of the given order as hypotheses, so that
`TauCeti.Geometry.Manifold.Sobolev.LocalMap.Atlas.Higher` reuses them at every order for
`2 < p < ∞`.

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

/-! ### Order zero -/

/-- At order zero, the local Sobolev maps on `s` are the maps continuous on `s`. -/
@[simp]
theorem memWkpLocMapOn_zero_iff : MemWkpLocMapOn I p 0 u s ↔ ContinuousOn u s :=
  ⟨MemWkpLocMapOnGroupoid.continuousOn, fun hu ↦ memWkpLocMapOn_iff.2
    ⟨hu, fun φ _ ψ _ ↦
      memWkpLoc_zero_iff.2 (φ.continuousOn_comp_comp_symm
        ((ψ.continuousOn_extend (I := I)).mono ψ.extend_source.ge) hu).memLpLoc⟩⟩

/-- At order zero, the local Sobolev maps are the continuous maps. -/
@[simp]
theorem memWkpLocMap_zero_iff : MemWkpLocMap I p 0 u ↔ Continuous u := by
  have h : MemWkpLocMapOn I p 0 u univ ↔ MemWkpLocMap I p 0 u :=
    memWkpLocMapOnGroupoid_univ
  rw [← h, memWkpLocMapOn_zero_iff, continuousOn_univ]

/-! ### Gluing coordinate expressions along changes of chart -/

/-- **Change of holomorphic chart.** Precomposition with the transition map `φ ∘ φ'⁻¹` between
two holomorphic charts preserves the local classes of order at most one. -/
private theorem memWkpLoc_comp_chart_transition {φ φ' : OpenPartialHomeomorph X ℂ}
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

/-- **Change of target chart through a `C^k` map.** Let the planar class `MemWkpLoc p _ k` be
preserved by composing continuous maps on open sets with `C^k` maps on open sets. If `ψ ∘ v` is a
continuous `W^{k,p}_loc` map on an open set `W` with `v` mapping `W` into the source of `ψ`, and
`f` is `C^k` on an open set containing `v '' W`, then `ψ' ∘ f ∘ v` is in `W^{k,p}_loc(W)` for every
chart `ψ'` of the target whose source contains `f '' (v '' W)`. -/
private theorem memWkpLoc_extend_comp [I.Boundaryless]
    (hchain : ∀ {v : ℂ → F} {g : F → F'} {W : Set ℂ} {O : Set F}, IsOpen W →
      MemWkpLoc p W k v → ContinuousOn v W → IsOpen O → ContDiffOn ℝ k g O → MapsTo v W O →
      MemWkpLoc p W k (g ∘ v))
    {ψ : OpenPartialHomeomorph M H} (hψ : ψ ∈ IsManifold.maximalAtlas I ∞ M)
    {ψ' : OpenPartialHomeomorph N H'} (hψ' : ψ' ∈ IsManifold.maximalAtlas I' ∞ N)
    {f : M → N} {t : Set M} (hf : ContMDiffOn I I' k f t) (ht : IsOpen t)
    {v : ℂ → M} {W : Set ℂ} (hW : IsOpen W) (hv : MemWkpLoc p W k (ψ.extend I ∘ v))
    (hvc : ContinuousOn (ψ.extend I ∘ v) W)
    (hmaps : MapsTo v W (ψ.source ∩ (t ∩ f ⁻¹' ψ'.source))) :
    MemWkpLoc p W k (ψ'.extend I' ∘ f ∘ v) := by
  have hO : IsOpen ((ψ.extend I).target ∩ (ψ.extend I).symm ⁻¹' (t ∩ f ⁻¹' ψ'.source)) :=
    ψ.continuousOn_extend_symm.isOpen_inter_preimage ψ.isOpen_extend_target
      (hf.continuousOn.isOpen_inter_preimage ht ψ'.open_source)
  have hsymm : ContMDiffOn 𝓘(ℝ, F) I k (ψ.extend I).symm (ψ.extend I).target := by
    rw [ψ.extend_target']
    exact (contMDiffOn_extend_symm hψ).of_le (by exact_mod_cast le_top)
  have hh : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, F') k (ψ'.extend I' ∘ f ∘ (ψ.extend I).symm)
      ((ψ.extend I).target ∩ (ψ.extend I).symm ⁻¹' (t ∩ f ⁻¹' ψ'.source)) :=
    ((ψ'.contMDiffOn_extend hψ').of_le (by exact_mod_cast le_top)).comp
      (hf.comp (hsymm.mono inter_subset_left) fun _ hy ↦ hy.2.1) fun _ hy ↦ hy.2.2
  have hmaps' : MapsTo (ψ.extend I ∘ v) W
      ((ψ.extend I).target ∩ (ψ.extend I).symm ⁻¹' (t ∩ f ⁻¹' ψ'.source)) := fun w hw ↦ by
    have hvw := hmaps hw
    refine ⟨(ψ.extend I).map_source (by simpa using hvw.1), ?_⟩
    simpa [ψ.left_inv hvw.1] using hvw.2
  refine (hchain hW hv hvc hO (contMDiffOn_iff_contDiffOn.1 hh) hmaps').congr_fun
    (fun w hw ↦ ?_) hW.measurableSet
  simp [ψ.left_inv (hmaps hw).1]

/-- **Chart independence from the planar calculus.** Let `k ≥ 1` be an order for which the planar
classes `MemWkpLoc p _ k` of maps into `F` are preserved by precomposition with transition maps of
holomorphic charts and by composing continuous maps on open sets with `C^k` maps on open sets.
Then for open `s` it suffices to test the coordinate expressions in the charts of a family `A` of
holomorphic charts covering `s` and a family `B` of smooth charts of `M` covering `u '' s`. -/
private theorem memWkpLocMapOn_iff_of_subset_maximalAtlas_of_planar [I.Boundaryless]
    [CompleteSpace F]
    (htrans : 1 ≤ k → ∀ {φ φ' : OpenPartialHomeomorph X ℂ},
      φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X → φ' ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X →
      ∀ {g : ℂ → F} {U W : Set ℂ}, IsOpen U → IsOpen W → MemWkpLoc p U k g →
      W ⊆ φ'.target ∩ φ'.symm ⁻¹' φ.source → MapsTo (φ ∘ φ'.symm) W U →
      MemWkpLoc p W k (g ∘ φ ∘ φ'.symm))
    (hchain : 1 ≤ k → ∀ {v : ℂ → F} {g : F → F} {W : Set ℂ} {O : Set F}, IsOpen W →
      MemWkpLoc p W k v → ContinuousOn v W → IsOpen O → ContDiffOn ℝ k g O → MapsTo v W O →
      MemWkpLoc p W k (g ∘ v))
    (hs : IsOpen s)
    {A : Set (OpenPartialHomeomorph X ℂ)} (hA : A ⊆ IsManifold.maximalAtlas 𝓘(ℂ) 1 X)
    (hAs : ∀ x ∈ s, ∃ φ ∈ A, x ∈ φ.source)
    {B : Set (OpenPartialHomeomorph M H)} (hB : B ⊆ IsManifold.maximalAtlas I ∞ M)
    (hBs : ∀ x ∈ s, ∃ ψ ∈ B, u x ∈ ψ.source) :
    MemWkpLocMapOn I p k u s ↔ ContinuousOn u s ∧ ∀ φ ∈ A, ∀ ψ ∈ B,
      MemWkpLoc p (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) k (ψ.extend I ∘ u ∘ φ.symm) := by
  refine ⟨fun hu ↦ ⟨hu.continuousOn, fun φ hφ ψ hψ ↦ hu.memWkpLoc_chart (hA hφ) (hB hψ)⟩,
    fun ⟨hc, h⟩ ↦ ?_⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact memWkpLocMapOn_zero_iff.2 hc
  refine memWkpLocMapOn_iff.2 ⟨hc, fun φ' hφ' ψ' hψ' ↦ ?_⟩
  -- Change the holomorphic chart, for each chart of `B`.
  have h1 : ∀ ψ ∈ B, MemWkpLoc p (φ'.target ∩ φ'.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) k
      (ψ.extend I ∘ u ∘ φ'.symm) := by
    intro ψ hψ
    refine memWkpLoc_iff_locally.2 fun z hz ↦ ?_
    obtain ⟨φ, hφA, hxφ⟩ := hAs _ hz.2.1
    have hO : IsOpen (φ'.target ∩ φ'.symm ⁻¹' φ.source) :=
      φ'.isOpen_inter_preimage_symm φ.open_source
    have hO' := (φ'.isOpen_inter_preimage_symm_inter_preimage hc hs ψ.open_source).inter hO
    refine ⟨_, inter_mem_nhdsWithin _ (hO.mem_nhds ⟨hz.1, hxφ⟩),
      (htrans hk (hA hφA) hφ' (φ.isOpen_inter_preimage_symm_inter_preimage hc hs ψ.open_source)
        hO' (h φ hφA ψ hψ) inter_subset_right fun w hw ↦ ?_).congr_fun (fun w hw ↦ ?_)
        hO'.measurableSet⟩
    · refine ⟨φ.map_source hw.2.2, ?_⟩
      simpa [Function.comp_apply, φ.left_inv hw.2.2] using hw.1.2
    · simp [φ.left_inv hw.2.2]
  -- Change the chart of `M`.
  refine memWkpLoc_iff_locally.2 fun z hz ↦ ?_
  obtain ⟨ψ, hψB, hxψ⟩ := hBs _ hz.2.1
  have hO := φ'.isOpen_inter_preimage_symm_inter_preimage hc hs ψ.open_source
  refine ⟨_, inter_mem_nhdsWithin _ (hO.mem_nhds ⟨hz.1, hz.2.1, hxψ⟩), ?_⟩
  exact memWkpLoc_extend_comp (hchain hk) (hB hψB) hψ' contMDiffOn_id isOpen_univ
    ((φ'.isOpen_inter_preimage_symm_inter_preimage hc hs ψ'.open_source).inter hO)
    ((h1 ψ hψB).mono inter_subset_right)
    ((φ'.continuousOn_comp_comp_symm (ψ.continuousOn_extend.mono ψ.extend_source.ge) hc).mono
      inter_subset_right)
    fun w hw ↦ ⟨hw.2.2.2, mem_univ _, hw.1.2.2⟩

/-- **Composition with `C^ℓ` maps from the planar calculus.** Let `k ≥ 1` be an order for which
the planar class `MemWkpLoc p _ k` is preserved by composing continuous maps into `F` on open sets
with `C^k` maps into `F'` on open sets. If `u` is a local Sobolev map of order `k` on an open set
`s`, mapping `s` into an open set `t` on which `f : M → N` is `C^ℓ` with `k ≤ ℓ`, then `f ∘ u` is a
local Sobolev map of order `k` on `s`. -/
private theorem MemWkpLocMapOn.contMDiffOn_comp_of_planar [IsManifold I ∞ M] [I.Boundaryless]
    [CompleteSpace F']
    (hchain : 1 ≤ k → ∀ {v : ℂ → F} {g : F → F'} {W : Set ℂ} {O : Set F}, IsOpen W →
      MemWkpLoc p W k v → ContinuousOn v W → IsOpen O → ContDiffOn ℝ k g O → MapsTo v W O →
      MemWkpLoc p W k (g ∘ v))
    {n : ℕ∞ω} {f : M → N} {t : Set M} (hu : MemWkpLocMapOn I p k u s)
    (hf : ContMDiffOn I I' n f t) (hkn : (k : ℕ∞ω) ≤ n) (hs : IsOpen s) (ht : IsOpen t)
    (hst : MapsTo u s t) : MemWkpLocMapOn I' p k (f ∘ u) s := by
  have hc : ContinuousOn (f ∘ u) s := hf.continuousOn.comp hu.continuousOn hst
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact memWkpLocMapOn_zero_iff.2 hc
  refine memWkpLocMapOn_iff.2 ⟨hc, fun φ hφ ψ' hψ' ↦ memWkpLoc_iff_locally.2 fun z hz ↦ ?_⟩
  have hO := φ.isOpen_inter_preimage_symm_inter_preimage hu.continuousOn hs
    (chartAt H (u (φ.symm z))).open_source
  refine ⟨_, inter_mem_nhdsWithin _ (hO.mem_nhds ⟨hz.1, hz.2.1, mem_chart_source _ _⟩), ?_⟩
  exact memWkpLoc_extend_comp (hchain hk) (IsManifold.chart_mem_maximalAtlas _) hψ'
    (hf.of_le hkn) ht ((φ.isOpen_inter_preimage_symm_inter_preimage hc hs ψ'.open_source).inter hO)
    ((hu.memWkpLoc_chart hφ (IsManifold.chart_mem_maximalAtlas _)).mono inter_subset_right)
    ((φ.continuousOn_comp_comp_symm ((chartAt H _).continuousOn_extend.mono
      (chartAt H _).extend_source.ge) hu.continuousOn).mono inter_subset_right)
    fun w hw ↦ ⟨hw.2.2.2, hst hw.2.2.1, hw.1.2.2⟩

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
      MemWkpLoc p (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) k (ψ.extend I ∘ u ∘ φ.symm) :=
  memWkpLocMapOn_iff_of_subset_maximalAtlas_of_planar
    (fun _ _ _ hφ hφ' _ _ _ _ _ hg hW hmaps ↦ memWkpLoc_comp_chart_transition hφ hφ' hk hg hW hmaps)
    (fun hk' _ _ _ _ _ hv hvc hO hg hmaps ↦ by
      obtain rfl := le_antisymm hk hk'
      exact hv.contDiffOn_comp hvc hO hg hmaps)
    hs hA hAs hB hBs

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

variable [IsManifold I ∞ M] [I.Boundaryless] [CompleteSpace F']

/-- **Composition with `C^ℓ` maps.** If `u` is a local Sobolev map of order `k ≤ 1` on an open set
`s`, mapping `s` into an open set `t` on which `f : M → N` is `C^ℓ` with `k ≤ ℓ`, then `f ∘ u` is a
local Sobolev map of order `k` on `s`. The manifold `N` may have corners. -/
theorem MemWkpLocMapOn.contMDiffOn_comp {n : ℕ∞ω} {f : M → N} {t : Set M}
    (hu : MemWkpLocMapOn I p k u s) (hk : k ≤ 1) (hf : ContMDiffOn I I' n f t)
    (hkn : (k : ℕ∞ω) ≤ n) (hs : IsOpen s) (ht : IsOpen t) (hst : MapsTo u s t) :
    MemWkpLocMapOn I' p k (f ∘ u) s :=
  hu.contMDiffOn_comp_of_planar (fun hk' _ _ _ _ _ hv hvc hO hg hmaps ↦ by
    obtain rfl := le_antisymm hk hk'
    exact hv.contDiffOn_comp hvc hO hg hmaps) hf hkn hs ht hst

/-- **Composition with `C^ℓ` maps.** If `u` is a local Sobolev map of order `k ≤ 1` and
`f : M → N` is `C^ℓ` with `k ≤ ℓ`, then `f ∘ u` is a local Sobolev map of order `k`. -/
theorem _root_.ContMDiff.comp_memWkpLocMap {n : ℕ∞ω} {f : M → N} (hf : ContMDiff I I' n f)
    (hu : MemWkpLocMap I p k u) (hk : k ≤ 1) (hkn : (k : ℕ∞ω) ≤ n) :
    MemWkpLocMap I' p k (f ∘ u) :=
  memWkpLocMapOnGroupoid_univ.mp (MemWkpLocMapOn.contMDiffOn_comp
    (memWkpLocMapOnGroupoid_univ.mpr hu) hk hf.contMDiffOn hkn
    isOpen_univ isOpen_univ (mapsTo_univ _ _))

variable [IsManifold I' ∞ N] [I'.Boundaryless] [CompleteSpace F]

/-- Composition with a `C^ℓ` diffeomorphism, `ℓ ≥ k`, preserves and reflects the local Sobolev
classes of order `k ≤ 1` on open sets. -/
theorem _root_.Diffeomorph.memWkpLocMapOn_diffeomorph_comp_iff {n : ℕ∞ω} (e : M ≃ₘ^n⟮I, I'⟯ N)
    (hk : k ≤ 1) (hkn : (k : ℕ∞ω) ≤ n) (hs : IsOpen s) :
    MemWkpLocMapOn I' p k (e ∘ u) s ↔ MemWkpLocMapOn I p k u s := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.contMDiffOn_comp hk e.contMDiff.contMDiffOn hkn hs isOpen_univ
    (mapsTo_univ _ _)⟩
  have := h.contMDiffOn_comp hk e.symm.contMDiff.contMDiffOn hkn hs isOpen_univ (mapsTo_univ _ _)
  simpa [Function.comp_def] using this

/-- Composition with a `C^ℓ` diffeomorphism, `ℓ ≥ k`, preserves and reflects the local Sobolev
classes of order `k ≤ 1`. -/
theorem _root_.Diffeomorph.memWkpLocMap_diffeomorph_comp_iff {n : ℕ∞ω} (e : M ≃ₘ^n⟮I, I'⟯ N)
    (hk : k ≤ 1) (hkn : (k : ℕ∞ω) ≤ n) :
    MemWkpLocMap I' p k (e ∘ u) ↔ MemWkpLocMap I p k u := by
  have h : MemWkpLocMapOn I p k u univ ↔ MemWkpLocMap I p k u :=
    memWkpLocMapOnGroupoid_univ
  have h' : MemWkpLocMapOn I' p k (e ∘ u) univ ↔ MemWkpLocMap I' p k (e ∘ u) :=
    memWkpLocMapOnGroupoid_univ
  rw [← h', ← h, e.memWkpLocMapOn_diffeomorph_comp_iff hk hkn isOpen_univ]

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
