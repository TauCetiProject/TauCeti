/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Sobolev.LocalMap.Atlas
-- Reuse its chart gluing proofs, parameterized by the planar calculus, privately.
import all TauCeti.Geometry.Manifold.Sobolev.LocalMap.Atlas
import TauCeti.Analysis.Sobolev.Local.ChainRule.Higher
import TauCeti.Analysis.Sobolev.Local.ChangeOfVariables.Higher
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
are glued with the locality of the planar classes, `memWkpLoc_iff_locally`, by the proofs of the
order-one file, which take the planar change of variables and chain rule as hypotheses.

## Main declarations

* `TauCeti.MemWkpLoc.comp_chart_transition`: for `1 ≤ p < ∞` and every order, precomposition with
  the transition map between two holomorphic charts preserves the planar classes of maps into a
  finite-dimensional space.
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

/-! ### Change of holomorphic chart -/

omit [FiniteDimensional ℝ F] in
/-- **Change of holomorphic chart at every order.** For `1 ≤ p < ∞` and every order `k`,
precomposition with the transition map `φ ∘ φ'⁻¹` between two holomorphic charts preserves the
local classes of order `k` of maps into a finite-dimensional space. -/
theorem MemWkpLoc.comp_chart_transition [Fact (1 ≤ p)] (hp' : p ≠ ⊤)
    {φ φ' : OpenPartialHomeomorph X ℂ}
    (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X) (hφ' : φ' ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {g : ℂ → E}
    {U W : Set ℂ} (hU : IsOpen U) (hWo : IsOpen W) (hg : MemWkpLoc p U k g)
    (hW : W ⊆ φ'.target ∩ φ'.symm ⁻¹' φ.source) (hmaps : MapsTo (φ ∘ φ'.symm) W U) :
    MemWkpLoc p W k (g ∘ φ ∘ φ'.symm) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact memWkpLoc_comp_chart_transition hφ hφ' zero_le_one hg hW hmaps
  have hφR := IsManifold.maximalAtlas_subset_restrictScalars_of_ne_zero k one_ne_zero hφ
  have hφ'R := IsManifold.maximalAtlas_subset_restrictScalars_of_ne_zero k one_ne_zero hφ'
  have hW' : W ⊆ (φ'.symm.trans φ).source := by
    simpa only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] using hW
  have hΦ : ContDiffOn ℝ k (φ ∘ φ'.symm) W := fun z hz ↦ by
    simpa only [OpenPartialHomeomorph.coe_trans] using
      (contDiffAt_symm_trans_of_mem_maximalAtlas hφ'R hφR (hW' hz)).contDiffWithinAt
  exact hg.comp_contDiffOn (U := ⟨W, hWo⟩) (V := ⟨U, hU⟩) hp' hk hΦ (fun z hz ↦ by
    obtain ⟨A, hA⟩ := exists_hasFDerivAt_symm_trans (by exact_mod_cast hk.ne') hφ'R hφR (hW' hz)
    rw [OpenPartialHomeomorph.coe_trans] at hA
    rw [hA.fderiv]
    exact A.toLinearEquiv.isUnit_det'.ne_zero) hmaps

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
      MemWkpLoc p (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) k (ψ.extend I ∘ u ∘ φ.symm) :=
  have : Fact (1 ≤ p) := ⟨one_le_two.trans hp.le⟩
  memWkpLocMapOn_iff_of_subset_maximalAtlas_of_planar
    (fun _ _ _ hφ hφ' _ _ _ hU hW hg hWs hmaps ↦
      hg.comp_chart_transition hp' hφ hφ' hU hW hWs hmaps)
    (fun hk _ _ _ _ hW hv hvc hO hg hmaps ↦
      hv.contDiffOn_comp_of_one_le hp hp' hk hW hvc hO hg hmaps)
    hs hA hAs hB hBs

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
    MemWkpLocMapOn I' p k (f ∘ u) s :=
  hu.contMDiffOn_comp_of_planar
    (fun hk _ _ _ _ hW hv hvc hO hg hmaps ↦
      hv.contDiffOn_comp_of_one_le hp hp' hk hW hvc hO hg hmaps)
    hf hkn hs ht hst

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
