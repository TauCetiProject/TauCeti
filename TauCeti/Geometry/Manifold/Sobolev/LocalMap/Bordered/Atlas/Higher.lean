/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Sobolev.LocalMap.Bordered.Atlas
-- Reuse its chart gluing proofs, parameterized by the planar calculus, privately.
import all TauCeti.Geometry.Manifold.Sobolev.LocalMap.Atlas
import TauCeti.Analysis.Sobolev.Local.ChainRule.HalfDisc
import TauCeti.Geometry.Manifold.Complex.ClosedUpperHalfPlane
import TauCeti.Geometry.Manifold.Sobolev.ChartTransition

/-!
# Chart calculus up to the boundary for local Sobolev maps of every order

Let `X` be a Riemann surface with boundary, charted on the closed upper half-plane with chart
changes in `TauCeti.borderedHolomorphicGroupoid`, and `M` a smooth manifold without boundary
modelled on a finite-dimensional real normed space, and let `2 < p < ∞`. For every order `k` and
open `s`, the local Sobolev class up to the boundary `TauCeti.MemWkpLocMapOnBordered I p k u s`
may be tested in the charts of any subfamilies of the maximal atlases covering `s` and `u '' s`,
and composition with `C^ℓ` maps, `ℓ ≥ k`, preserves it. The file
`TauCeti.Geometry.Manifold.Sobolev.LocalMap.Bordered.Atlas` proves chart independence for
`k ≤ 1` and every exponent.

The coordinate domains `(φ.extend closedUpperHalfPlaneModel).target ∩ _ ⁻¹' T`, for open `T`, are
the half-discs `Ω ∩ {0 ≤ im}` with `Ω` open in `ℂ`
(`OpenPartialHomeomorph.exists_isOpen_extend_target_inter_preimage`). A change of bordered
holomorphic chart preserves the half-disc classes of every order
(`TauCeti.MemWkpLoc.comp_bordered_transition`, in
`TauCeti.Geometry.Manifold.Sobolev.ChartTransition`), through its Schwarz reflection. Changing
the chart of `M`, or composing with a `C^ℓ` map, is the half-disc chain rule
`TauCeti.MemWkpLoc.contDiffOn_comp_succ_halfPlane` for continuous maps, which needs `p > 2`. The
steps are glued by the proofs of the order-one file, which take the planar change of variables and
chain rule as hypotheses.

## Main declarations

* `TauCeti.memWkpLocMapOnBordered_iff_of_subset_maximalAtlas_of_two_lt`: **chart independence**
  up to the boundary at every order, testing families of charts covering `s` and `u '' s`;
  `TauCeti.memWkpLocMapOnBordered_iff_atlas_of_two_lt` and
  `TauCeti.memWkpLocMapOnBordered_iff_chartAt_of_two_lt` for the atlases and the preferred
  charts, and the versions for `TauCeti.MemWkpLocMapBordered`;
  `TauCeti.memWkpLocMapOnBordered_of_memWkpLoc_chart` tests a single pair of charts.
* `TauCeti.MemWkpLocMapOnBordered.contMDiffOn_comp_of_two_lt`,
  `ContMDiff.comp_memWkpLocMapBordered_of_two_lt`: composition with `C^ℓ` maps, `ℓ ≥ k`, into any
  manifold modelled on a finite-dimensional real normed space.
* `Diffeomorph.memWkpLocMapOnBordered_diffeomorph_comp_iff_of_two_lt`,
  `Diffeomorph.memWkpLocMapBordered_diffeomorph_comp_iff_of_two_lt`: invariance under `C^ℓ`
  diffeomorphisms of the target, `ℓ ≥ k`.

## Implementation notes

As for surfaces without boundary (`TauCeti.Geometry.Manifold.Sobolev.LocalMap.Atlas.Higher`), the
target `M` is assumed boundaryless, while the target `N` of a composition may have corners, and the
model spaces are finite-dimensional because the planar chain rule and change of variables of every
order are proved for finite-dimensional values.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 and Section 2.4.
-/

public section

open Set Filter MeasureTheory TopologicalSpace
open scoped Manifold ContDiff Topology NNReal

noncomputable section

namespace TauCeti

open ClosedUpperHalfPlane

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ClosedUpperHalfPlane X]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] [FiniteDimensional ℝ F']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ F' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {p : ENNReal} {k : ℕ} {u : X → M} {s : Set X}

/-! ### Composition in coordinates -/

omit [ChartedSpace ClosedUpperHalfPlane X] in
/-- **Composition in a coordinate domain up to the boundary.** For `2 < p < ∞` and `k ≥ 1`, a
continuous map of the local class of order `k` on the half-disc over an open set `T` in a bordered
holomorphic chart, composed with a map that is `C^k` on an open set containing its image, stays in
that class. -/
private theorem MemWkpLoc.contDiffOn_comp_extend_target (hp : 2 < p) (hp' : p ≠ ⊤) (hk : 1 ≤ k)
    {φ : OpenPartialHomeomorph X ClosedUpperHalfPlane} {T : Set X} (hT : IsOpen T)
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    {w : ℂ → F} {g : F → G} {O : Set F}
    (hw : MemWkpLoc p ((φ.extend closedUpperHalfPlaneModel).target ∩
      (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' T) k w)
    (hwc : ContinuousOn w ((φ.extend closedUpperHalfPlaneModel).target ∩
      (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' T))
    (hO : IsOpen O) (hg : ContDiffOn ℝ k g O)
    (hmaps : MapsTo w ((φ.extend closedUpperHalfPlaneModel).target ∩
      (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' T) O) :
    MemWkpLoc p ((φ.extend closedUpperHalfPlaneModel).target ∩
      (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' T) k (g ∘ w) := by
  lift p to ℝ≥0 using hp'
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hk
  obtain ⟨Ω, hΩ, hV⟩ := φ.exists_isOpen_extend_target_inter_preimage hT
  rw [hV] at hw hwc hmaps ⊢
  exact MemWkpLoc.contDiffOn_comp_succ_halfPlane (Ω := ⟨Ω, hΩ⟩) (u := w) (g := g) (W := O)
    (by exact_mod_cast hp) hw hwc hO (by exact_mod_cast hg) hmaps

/-! ### Chart independence -/

section ChartIndependence

variable [I.Boundaryless]

/-- **Chart independence of the local Sobolev class up to the boundary at every order.** For
`2 < p < ∞`, every order `k` and open `s`, it suffices to test the coordinate expressions in the
charts of a family `A` of bordered holomorphic charts covering `s` and a family `B` of smooth
charts of `M` covering `u '' s`. -/
theorem memWkpLocMapOnBordered_iff_of_subset_maximalAtlas_of_two_lt (hp : 2 < p) (hp' : p ≠ ⊤)
    (hs : IsOpen s) {A : Set (OpenPartialHomeomorph X ClosedUpperHalfPlane)}
    (hA : A ⊆ borderedHolomorphicGroupoid.maximalAtlas X) (hAs : ∀ x ∈ s, ∃ φ ∈ A, x ∈ φ.source)
    {B : Set (OpenPartialHomeomorph M H)} (hB : B ⊆ IsManifold.maximalAtlas I ∞ M)
    (hBs : ∀ x ∈ s, ∃ ψ ∈ B, u x ∈ ψ.source) :
    MemWkpLocMapOnBordered I p k u s ↔ ContinuousOn u s ∧ ∀ φ ∈ A, ∀ ψ ∈ B,
      MemWkpLoc p ((φ.extend closedUpperHalfPlaneModel).target ∩
        (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) k
        (ψ.extend I ∘ u ∘ (φ.extend closedUpperHalfPlaneModel).symm) :=
  have : Fact (1 ≤ p) := ⟨one_le_two.trans hp.le⟩
  memWkpLocMapOnGroupoid_iff_of_subset_maximalAtlas_of_planar
    (fun _ _ _ hφ hφ' _ _ _ hT hT' hg hW hmaps ↦
      hg.comp_bordered_transition hφ hφ' hT hT' hW hmaps)
    (fun hk _ _ _ _ _ _ hT hw hwc hO hg hmaps ↦
      hw.contDiffOn_comp_extend_target hp hp' hk hT hwc hO hg hmaps)
    hs hA hAs hB hBs

/-- **Chart independence up to the boundary on the whole surface at every order.** For
`2 < p < ∞` and every order `k`, it suffices to test the coordinate expressions in the charts of a
family `A` of bordered holomorphic charts covering `X` and a family `B` of smooth charts covering
the image of `u`. -/
theorem memWkpLocMapBordered_iff_of_subset_maximalAtlas_of_two_lt (hp : 2 < p) (hp' : p ≠ ⊤)
    {A : Set (OpenPartialHomeomorph X ClosedUpperHalfPlane)}
    (hA : A ⊆ borderedHolomorphicGroupoid.maximalAtlas X) (hAs : ∀ x, ∃ φ ∈ A, x ∈ φ.source)
    {B : Set (OpenPartialHomeomorph M H)} (hB : B ⊆ IsManifold.maximalAtlas I ∞ M)
    (hBs : ∀ x, ∃ ψ ∈ B, u x ∈ ψ.source) :
    MemWkpLocMapBordered I p k u ↔ Continuous u ∧ ∀ φ ∈ A, ∀ ψ ∈ B,
      MemWkpLoc p ((φ.extend closedUpperHalfPlaneModel).target ∩
        (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' (u ⁻¹' ψ.source)) k
        (ψ.extend I ∘ u ∘ (φ.extend closedUpperHalfPlaneModel).symm) := by
  have h : MemWkpLocMapOnBordered I p k u univ ↔ MemWkpLocMapBordered I p k u :=
    memWkpLocMapOnGroupoid_univ
  rw [← h, memWkpLocMapOnBordered_iff_of_subset_maximalAtlas_of_two_lt hp hp' isOpen_univ hA
    (fun x _ ↦ hAs x) hB (fun x _ ↦ hBs x)]
  simp only [continuousOn_univ, univ_inter]

/-- **Testing one pair of charts.** For `2 < p < ∞`, a map continuous on an open set `t` inside
the source of a bordered holomorphic chart `φ`, mapping `t` into the source of a smooth chart `χ`
of `M`, is a local Sobolev map up to the boundary of order `k` on `t` as soon as its coordinate
expression in `φ` and `χ` is in the planar class of order `k` over `t`. -/
theorem memWkpLocMapOnBordered_of_memWkpLoc_chart (hp : 2 < p) (hp' : p ≠ ⊤) {t : Set X}
    (ht : IsOpen t) {φ : OpenPartialHomeomorph X ClosedUpperHalfPlane}
    (hφ : φ ∈ borderedHolomorphicGroupoid.maximalAtlas X) (htφ : t ⊆ φ.source)
    {χ : OpenPartialHomeomorph M H} (hχ : χ ∈ IsManifold.maximalAtlas I ∞ M)
    (htχ : MapsTo u t χ.source) (hu : ContinuousOn u t)
    (h : MemWkpLoc p ((φ.extend closedUpperHalfPlaneModel).target ∩
      (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' t) k
        (χ.extend I ∘ u ∘ (φ.extend closedUpperHalfPlaneModel).symm)) :
    MemWkpLocMapOnBordered I p k u t := by
  refine (memWkpLocMapOnBordered_iff_of_subset_maximalAtlas_of_two_lt hp hp' ht (A := {φ})
    (singleton_subset_iff.2 hφ) (fun x hx ↦ ⟨φ, mem_singleton φ, htφ hx⟩) (B := {χ})
    (singleton_subset_iff.2 hχ) fun x hx ↦ ⟨χ, mem_singleton χ, htχ hx⟩).2 ⟨hu, ?_⟩
  intro φ' hφ' χ' hχ'
  rw [mem_singleton_iff] at hφ' hχ'
  subst hφ' hχ'
  rwa [inter_eq_left.2 (mapsTo_iff_subset_preimage.1 htχ)]

variable [HasGroupoid X borderedHolomorphicGroupoid] [IsManifold I ∞ M]

/-- Chart independence up to the boundary at every order: for `2 < p < ∞` and open `s`, it
suffices to test the charts of the atlases of `X` and `M`. -/
theorem memWkpLocMapOnBordered_iff_atlas_of_two_lt (hp : 2 < p) (hp' : p ≠ ⊤) (hs : IsOpen s) :
    MemWkpLocMapOnBordered I p k u s ↔ ContinuousOn u s ∧
      ∀ φ ∈ atlas ClosedUpperHalfPlane X, ∀ ψ ∈ atlas H M,
        MemWkpLoc p ((φ.extend closedUpperHalfPlaneModel).target ∩
          (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) k
          (ψ.extend I ∘ u ∘ (φ.extend closedUpperHalfPlaneModel).symm) :=
  memWkpLocMapOnBordered_iff_of_subset_maximalAtlas_of_two_lt hp hp' hs
    borderedHolomorphicGroupoid.subset_maximalAtlas
    (fun x _ ↦ ⟨_, chart_mem_atlas _ x, mem_chart_source _ x⟩) IsManifold.subset_maximalAtlas
    fun x _ ↦ ⟨_, chart_mem_atlas H (u x), mem_chart_source H (u x)⟩

/-- Chart independence up to the boundary at every order: for `2 < p < ∞`, it suffices to test
the charts of the atlases of `X` and `M`. -/
theorem memWkpLocMapBordered_iff_atlas_of_two_lt (hp : 2 < p) (hp' : p ≠ ⊤) :
    MemWkpLocMapBordered I p k u ↔ Continuous u ∧
      ∀ φ ∈ atlas ClosedUpperHalfPlane X, ∀ ψ ∈ atlas H M,
        MemWkpLoc p ((φ.extend closedUpperHalfPlaneModel).target ∩
          (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' (u ⁻¹' ψ.source)) k
          (ψ.extend I ∘ u ∘ (φ.extend closedUpperHalfPlaneModel).symm) :=
  memWkpLocMapBordered_iff_of_subset_maximalAtlas_of_two_lt hp hp'
    borderedHolomorphicGroupoid.subset_maximalAtlas
    (fun x ↦ ⟨_, chart_mem_atlas _ x, mem_chart_source _ x⟩) IsManifold.subset_maximalAtlas
    fun x ↦ ⟨_, chart_mem_atlas H (u x), mem_chart_source H (u x)⟩

/-- Chart independence up to the boundary at every order: for `2 < p < ∞` and open `s`, it
suffices to test the preferred charts of `X` and `M`. -/
theorem memWkpLocMapOnBordered_iff_chartAt_of_two_lt (hp : 2 < p) (hp' : p ≠ ⊤)
    (hs : IsOpen s) :
    MemWkpLocMapOnBordered I p k u s ↔ ContinuousOn u s ∧ ∀ x : X, ∀ y : M,
      MemWkpLoc p ((extChartAt closedUpperHalfPlaneModel x).target ∩
        (extChartAt closedUpperHalfPlaneModel x).symm ⁻¹' (s ∩ u ⁻¹' (chartAt H y).source)) k
        (extChartAt I y ∘ u ∘ (extChartAt closedUpperHalfPlaneModel x).symm) := by
  rw [memWkpLocMapOnBordered_iff_of_subset_maximalAtlas_of_two_lt hp hp' hs
    (A := range (chartAt ClosedUpperHalfPlane))
    (range_subset_iff.2 borderedHolomorphicGroupoid.chart_mem_maximalAtlas)
    (fun x _ ↦ ⟨_, mem_range_self x, mem_chart_source _ x⟩)
    (B := range (chartAt H)) (range_subset_iff.2 IsManifold.chart_mem_maximalAtlas)
    fun x _ ↦ ⟨_, mem_range_self (u x), mem_chart_source H (u x)⟩]
  simp only [forall_mem_range, extChartAt]

/-- Chart independence up to the boundary at every order: for `2 < p < ∞`, it suffices to test
the preferred charts of `X` and `M`. -/
theorem memWkpLocMapBordered_iff_chartAt_of_two_lt (hp : 2 < p) (hp' : p ≠ ⊤) :
    MemWkpLocMapBordered I p k u ↔ Continuous u ∧ ∀ x : X, ∀ y : M,
      MemWkpLoc p ((extChartAt closedUpperHalfPlaneModel x).target ∩
        (extChartAt closedUpperHalfPlaneModel x).symm ⁻¹' (u ⁻¹' (chartAt H y).source)) k
        (extChartAt I y ∘ u ∘ (extChartAt closedUpperHalfPlaneModel x).symm) := by
  have h : MemWkpLocMapOnBordered I p k u univ ↔ MemWkpLocMapBordered I p k u :=
    memWkpLocMapOnGroupoid_univ
  rw [← h, memWkpLocMapOnBordered_iff_chartAt_of_two_lt hp hp' isOpen_univ]
  simp only [continuousOn_univ, univ_inter]

end ChartIndependence

/-! ### Composition with differentiable maps -/

section Composition

variable [IsManifold I ∞ M] [I.Boundaryless]

/-- **Composition with `C^ℓ` maps up to the boundary at every order.** Let `2 < p < ∞`. If `u` is
a local Sobolev map up to the boundary of order `k` on an open set `s`, mapping `s` into an open
set `t` on which `f : M → N` is `C^ℓ` with `k ≤ ℓ`, then `f ∘ u` is a local Sobolev map up to the
boundary of order `k` on `s`. The manifold `N` may have corners. -/
theorem MemWkpLocMapOnBordered.contMDiffOn_comp_of_two_lt {n : ℕ∞ω} {f : M → N} {t : Set M}
    (hu : MemWkpLocMapOnBordered I p k u s) (hp : 2 < p) (hp' : p ≠ ⊤)
    (hf : ContMDiffOn I I' n f t) (hkn : (k : ℕ∞ω) ≤ n) (hs : IsOpen s) (ht : IsOpen t)
    (hst : MapsTo u s t) : MemWkpLocMapOnBordered I' p k (f ∘ u) s :=
  MemWkpLocMapOnGroupoid.contMDiffOn_comp_of_planar
    (fun hk _ _ _ _ _ _ hT hw hwc hO hg hmaps ↦
      hw.contDiffOn_comp_extend_target hp hp' hk hT hwc hO hg hmaps)
    hu hf hkn hs ht hst

/-- **Composition with `C^ℓ` maps up to the boundary at every order.** Let `2 < p < ∞`. If `u` is
a local Sobolev map up to the boundary of order `k` and `f : M → N` is `C^ℓ` with `k ≤ ℓ`, then
`f ∘ u` is a local Sobolev map up to the boundary of order `k`. -/
theorem _root_.ContMDiff.comp_memWkpLocMapBordered_of_two_lt {n : ℕ∞ω} {f : M → N}
    (hf : ContMDiff I I' n f) (hu : MemWkpLocMapBordered I p k u) (hp : 2 < p) (hp' : p ≠ ⊤)
    (hkn : (k : ℕ∞ω) ≤ n) : MemWkpLocMapBordered I' p k (f ∘ u) :=
  memWkpLocMapOnGroupoid_univ.mp (MemWkpLocMapOnBordered.contMDiffOn_comp_of_two_lt
    (memWkpLocMapOnGroupoid_univ.mpr hu) hp hp' hf.contMDiffOn hkn
    isOpen_univ isOpen_univ (mapsTo_univ _ _))

variable [IsManifold I' ∞ N] [I'.Boundaryless]

/-- Composition with a `C^ℓ` diffeomorphism, `ℓ ≥ k`, preserves and reflects the local Sobolev
classes up to the boundary of every order `k` on open sets, for `2 < p < ∞`. -/
theorem _root_.Diffeomorph.memWkpLocMapOnBordered_diffeomorph_comp_iff_of_two_lt {n : ℕ∞ω}
    (e : M ≃ₘ^n⟮I, I'⟯ N) (hp : 2 < p) (hp' : p ≠ ⊤) (hkn : (k : ℕ∞ω) ≤ n) (hs : IsOpen s) :
    MemWkpLocMapOnBordered I' p k (e ∘ u) s ↔ MemWkpLocMapOnBordered I p k u s := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.contMDiffOn_comp_of_two_lt hp hp' e.contMDiff.contMDiffOn hkn hs
    isOpen_univ (mapsTo_univ _ _)⟩
  have := MemWkpLocMapOnBordered.contMDiffOn_comp_of_two_lt h hp hp'
    e.symm.contMDiff.contMDiffOn hkn hs isOpen_univ (mapsTo_univ _ _)
  simpa [Function.comp_def] using this

/-- Composition with a `C^ℓ` diffeomorphism, `ℓ ≥ k`, preserves and reflects the local Sobolev
classes up to the boundary of every order `k`, for `2 < p < ∞`. -/
theorem _root_.Diffeomorph.memWkpLocMapBordered_diffeomorph_comp_iff_of_two_lt {n : ℕ∞ω}
    (e : M ≃ₘ^n⟮I, I'⟯ N) (hp : 2 < p) (hp' : p ≠ ⊤) (hkn : (k : ℕ∞ω) ≤ n) :
    MemWkpLocMapBordered I' p k (e ∘ u) ↔ MemWkpLocMapBordered I p k u := by
  have h : MemWkpLocMapOnBordered I p k u univ ↔ MemWkpLocMapBordered I p k u :=
    memWkpLocMapOnGroupoid_univ
  have h' : MemWkpLocMapOnBordered I' p k (e ∘ u) univ ↔ MemWkpLocMapBordered I' p k (e ∘ u) :=
    memWkpLocMapOnGroupoid_univ
  rw [← h', ← h, e.memWkpLocMapOnBordered_diffeomorph_comp_iff_of_two_lt hp hp' hkn isOpen_univ]

end Composition

end TauCeti
