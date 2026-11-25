/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.AEZeroOff
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Bordered.ExtensionByZero
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Bordered.SMul

/-!
# Bordered Sobolev sections vanishing off a set, and extension by zero from one chart

Let `M` be a manifold modelled on the closed upper half-plane, let `V → M` be a real vector bundle
with finite-dimensional model fibre `F`, and let `A` be a finite bundle atlas. This file is the
analogue for bases with boundary of `TauCeti.Geometry.Manifold.VectorBundle.Sobolev.AEZeroOff`.

For a set `L ⊆ M`, `TauCeti.BorderedSobolevSection.aeZeroOff A p k L` is the closed subspace of
`W^{k,p}(V)` of the elements whose chart data vanish almost everywhere over the complement of `L`.
For `L` inside the domain of chart `i`, such an element is determined by its chart-`i` components
(`TauCeti.BorderedSobolevSection.chartRestrictL_injective`), which lie in the closed subspace
`TauCeti.BorderedSobolevSection.chartAeZeroOff A p k i L` of chart-`i` tuples vanishing almost
everywhere off `L`. For closed `L` and a `Cⁿ` bundle with `1 ≤ n` and `k ≤ n`, every such tuple
arises in this way (`TauCeti.BorderedSobolevSection.chartRestrictL_surjective`, from the extension
by zero `TauCeti.BorderedSobolevSection.exists_chartValueL_ae_eq_halfCoord_of_eq_zero`). So the
chart-`i` components form a linear equivalence
(`TauCeti.BorderedSobolevSection.chartRestrictEquiv`). Its inverse followed by the inclusion is the
extension by zero `TauCeti.BorderedSobolevSection.extendByZeroL`, which is continuous by the closed
graph theorem.

All of this specializes the construction for general chart data in
`TauCeti.Geometry.Manifold.VectorBundle.Sobolev.AEZeroOff` (`TauCeti.SectionChartData.aeZeroOn`,
`TauCeti.SectionChartData.chartRestrictL`, `TauCeti.SectionChartData.extendByZeroL`) to the chart
data `A.halfSectionChartData`; only the surjectivity is specific to bases with boundary.

## Main definitions

* `TauCeti.BorderedSobolevSection.aeZeroOff`: the elements of `W^{k,p}(V)` vanishing almost
  everywhere off a set `L ⊆ M`.
* `TauCeti.BorderedSobolevSection.chartAeZeroOff`: the tuples of chart-`i` Sobolev functions
  vanishing almost everywhere off `L`.
* `TauCeti.BorderedSobolevSection.chartRestrictL`: the chart-`i` components of an element
  vanishing off `L`.
* `TauCeti.BorderedSobolevSection.chartRestrictEquiv`,
  `TauCeti.BorderedSobolevSection.extendByZeroL`: for closed `L` inside the domain of chart `i`,
  the chart-`i` components as a linear equivalence, and its inverse, extension by zero, as a
  continuous linear map.

## Main results

* `TauCeti.BorderedSobolevSection.isClosed_aeZeroOff`,
  `TauCeti.BorderedSobolevSection.isClosed_chartAeZeroOff`: both subspaces are closed.
* `TauCeti.BorderedSobolevSection.mem_aeZeroOff_of_ae_eq_halfCoord`: an element given by a section
  vanishing off `L` vanishes off `L`.
* `TauCeti.BorderedSobolevSection.contMDiffSMulL_mem_aeZeroOff`: `φ • w` vanishes off
  `tsupport φ`.
* `TauCeti.BorderedSobolevSection.chartRestrictL_injective`,
  `TauCeti.BorderedSobolevSection.chartRestrictL_surjective`: the chart-`i` components of the
  elements vanishing off a closed subset `L` of the domain of chart `i` are a bijection onto the
  chart-`i` tuples vanishing off `L`.
* `TauCeti.BorderedSobolevSection.extendByZeroL_mem_aeZeroOff`,
  `TauCeti.BorderedSobolevSection.chartRestrictL_extendByZeroL`,
  `TauCeti.BorderedSobolevSection.extendByZeroL_chartRestrictL`: the extension by zero vanishes
  off `L` and is inverse to taking chart-`i` components.
* `TauCeti.BorderedSobolevSection.tendsto_of_tendsto_chartRestrictL`: elements vanishing off `L`
  converge when their chart-`i` components do.

## References

* R. S. Palais, *Foundations of Global Non-linear Analysis*, Benjamin (1968), §9.
-/

public section

noncomputable section

open Bundle Filter MeasureTheory Module Set TopologicalSpace
open scoped Manifold ContDiff ENNReal Topology

namespace TauCeti

open FiniteBundleAtlas

namespace BorderedSobolevSection

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ClosedUpperHalfPlane M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  (A : FiniteBundleAtlas ClosedUpperHalfPlane M F V) (p : ℝ≥0∞) [Fact (1 ≤ p)] (k : ℕ)

/-- The elements of `W^{k,p}(V)` vanishing almost everywhere off a set `L ⊆ M`: in every chart
`i` the chart data vanish almost everywhere at the points of `A.halfImage i` lying over the
complement of `L`. For closed `L` these are the elements supported in `L`. -/
abbrev aeZeroOff (L : Set M) : Submodule ℝ (BorderedSobolevSection A p k) :=
  A.halfSectionChartData.aeZeroOn volume p k fun i ↦
    {z | (A.chart i).symm (closedUpperHalfPlaneModel.symm z) ∉ L}

variable {A p k} in
theorem mem_aeZeroOff {L : Set M} {w : BorderedSobolevSection A p k} :
    w ∈ aeZeroOff A p k L ↔ ∀ i, ∀ᵐ z ∂volume.restrict (A.halfImage i : Set ℂ),
      (A.chart i).symm (closedUpperHalfPlaneModel.symm z) ∉ L →
        A.halfSectionChartData.chartValueL volume p k i w z = 0 :=
  SectionChartData.mem_aeZeroOn

variable {A p k} in
theorem aeZeroOff_mono {L L' : Set M} (h : L ⊆ L') :
    aeZeroOff A p k L ≤ aeZeroOff A p k L' :=
  SectionChartData.aeZeroOn_mono fun _ _ hz h' ↦ hz (h h')

/-- The elements of `W^{k,p}(V)` vanishing off `L` form a closed subspace. -/
theorem isClosed_aeZeroOff (L : Set M) :
    IsClosed (aeZeroOff A p k L : Set (BorderedSobolevSection A p k)) :=
  A.halfSectionChartData.isClosed_aeZeroOn volume p k _

/-- The tuples of chart-`i` Sobolev functions, one for each vector of the basis
`Module.finBasis ℝ F`, vanishing almost everywhere at the points of `A.halfImage i` lying over the
complement of `L ⊆ M`. -/
abbrev chartAeZeroOff (i : Fin A.n) (L : Set M) :
    Submodule ℝ (Fin (finrank ℝ F) → Wkp volume (A.halfImage i) p k) :=
  A.halfSectionChartData.chartAeZeroOn volume p k i
    {z | (A.chart i).symm (closedUpperHalfPlaneModel.symm z) ∉ L}

omit [FiniteDimensional ℝ F] in
variable {A p k} in
theorem mem_chartAeZeroOff {i : Fin A.n} {L : Set M}
    {g : Fin (finrank ℝ F) → Wkp volume (A.halfImage i) p k} :
    g ∈ chartAeZeroOff A p k i L ↔ ∀ j, ∀ᵐ z ∂volume.restrict (A.halfImage i : Set ℂ),
      (A.chart i).symm (closedUpperHalfPlaneModel.symm z) ∉ L → Wkp.value k (g j) z = 0 :=
  SectionChartData.mem_chartAeZeroOn

omit [FiniteDimensional ℝ F] in
/-- The chart-`i` tuples vanishing off `L` form a closed subspace. -/
theorem isClosed_chartAeZeroOff (i : Fin A.n) (L : Set M) :
    IsClosed (chartAeZeroOff A p k i L :
      Set (Fin (finrank ℝ F) → Wkp volume (A.halfImage i) p k)) :=
  A.halfSectionChartData.isClosed_chartAeZeroOn volume p k i _

variable {A p k} in
/-- The chart-`i` components of an element vanishing off `L` vanish off `L`. -/
theorem mem_chartAeZeroOff_of_mem_aeZeroOff {L : Set M} {w : BorderedSobolevSection A p k}
    (hw : w ∈ aeZeroOff A p k L) (i : Fin A.n) :
    (w : A.halfSectionChartData.SobolevData volume p k) i ∈ chartAeZeroOff A p k i L :=
  SectionChartData.mem_chartAeZeroOn_of_mem_aeZeroOn hw i

/-- The chart-`i` components of the elements of `W^{k,p}(V)` vanishing off `L`, as a continuous
linear map into the chart-`i` tuples vanishing off `L`. -/
def chartRestrictL (i : Fin A.n) (L : Set M) :
    aeZeroOff A p k L →L[ℝ] chartAeZeroOff A p k i L :=
  A.halfSectionChartData.chartRestrictL volume p k _ i

@[simp]
theorem coe_chartRestrictL_apply (i : Fin A.n) (L : Set M) (w : aeZeroOff A p k L) :
    (chartRestrictL A p k i L w : Fin (finrank ℝ F) → Wkp volume (A.halfImage i) p k) =
      ((w : BorderedSobolevSection A p k) : A.halfSectionChartData.SobolevData volume p k) i :=
  A.halfSectionChartData.coe_chartRestrictL_apply volume p k _ i w

variable {A p k}

/-- If the chart data of `w` are the readings of a section `s`, then the chart-`i` components of
`w` are the coordinates of `A.halfCoord i s` in the basis `Module.finBasis ℝ F`. -/
theorem value_ae_eq_repr_halfCoord {w : BorderedSobolevSection A p k} {s : ∀ x, V x}
    {i : Fin A.n}
    (hs : A.halfSectionChartData.chartValueL volume p k i w
      =ᵐ[volume.restrict (A.halfImage i : Set ℂ)] A.halfCoord i s)
    (j : Fin (finrank ℝ F)) :
    (Wkp.value k ((w : A.halfSectionChartData.SobolevData volume p k) i j) : ℂ → ℝ)
      =ᵐ[volume.restrict (A.halfImage i : Set ℂ)]
        fun z ↦ (finBasis ℝ F).repr (A.halfCoord i s z) j := by
  filter_upwards [SectionChartData.value_ae_eq_repr_coord
      (hs.trans (A.halfSectionChartData_coord_ae_eq i s).symm) j,
    ae_restrict_mem (A.halfImage i).isOpen.measurableSet] with z h hz
  rw [h, A.halfSectionChartData_coord_of_mem _ hz]

/-- An element whose chart data are the readings of a section vanishing off `L` vanishes almost
everywhere off `L`. -/
theorem mem_aeZeroOff_of_ae_eq_halfCoord {L : Set M} {w : BorderedSobolevSection A p k}
    {s : ∀ x, V x}
    (hs : ∀ i, A.halfSectionChartData.chartValueL volume p k i w
      =ᵐ[volume.restrict (A.halfImage i : Set ℂ)] A.halfCoord i s)
    (hsL : ∀ x ∉ L, s x = 0) : w ∈ aeZeroOff A p k L := mem_aeZeroOff.2 fun i ↦ by
  filter_upwards [hs i, ae_restrict_mem (A.halfImage i).isOpen.measurableSet] with z hz hzi hL
  rw [hz, halfCoord_def]
  exact A.coord_eq_zero (A.mem_halfImage.1 hzi).1 (hsL _ hL)

/-- Multiplication by a smooth function `φ` takes values in the elements vanishing off
`tsupport φ`. -/
theorem contMDiffSMulL_mem_aeZeroOff [IsManifold closedUpperHalfPlaneModel ∞ M] {φ : M → ℝ}
    (hφ : ContMDiff closedUpperHalfPlaneModel 𝓘(ℝ) ∞ φ) (w : BorderedSobolevSection A p k) :
    contMDiffSMulL A p k hφ w ∈ aeZeroOff A p k (tsupport φ) := mem_aeZeroOff.2 fun i ↦ by
  filter_upwards [chartValueL_contMDiffSMulL_ae hφ w i] with y hy hL
  rw [hy, image_eq_zero_of_notMem_tsupport hL, zero_smul]

/-- An element vanishing off a subset `L` of the domain of chart `i` is determined by its
chart-`i` components: over `L` its components in every other chart are coordinate changes of its
chart-`i` components. -/
theorem chartRestrictL_injective [IsManifold closedUpperHalfPlaneModel 1 M] {i : Fin A.n}
    {L : Set M} (hLi : L ⊆ A.dom i) : Function.Injective (chartRestrictL A p k i L) :=
  SectionChartData.chartRestrictL_injective A.aeTransition_halfSectionChartData
    fun i' z hz hL ↦ by
      obtain ⟨hzi, hz0⟩ := A.mem_halfImage.1 hz
      obtain ⟨x, hx, hxz⟩ := A.mem_image.1 hzi
      rw [mem_ofPred_eq, not_not, ← hxz,
        (A.chart i').left_inv (A.dom_subset_chart_source i' hx)] at hL
      refine A.mem_halfOverlap.2 ⟨?_, hz0⟩
      rw [← hxz]
      exact A.chart_mem_overlap (hLi hL) hx

/-- **Extension by zero.** For a `Cⁿ` bundle with `1 ≤ n` and `k ≤ n`, every tuple of chart-`i`
Sobolev functions vanishing almost everywhere off a closed subset `L` of the domain of chart `i`
consists of the chart-`i` components of an element of `W^{k,p}(V)` vanishing off `L`. -/
theorem chartRestrictL_surjective {n : ℕ} [IsManifold closedUpperHalfPlaneModel n M]
    [ContMDiffVectorBundle n F V closedUpperHalfPlaneModel] (hn : 1 ≤ n) (hkn : k ≤ n)
    {i : Fin A.n} {L : Set M} (hL : IsClosed L) (hLi : L ⊆ A.dom i) :
    Function.Surjective (chartRestrictL A p k i L) := by
  classical
  intro g
  -- The section equal in chart `i` to the tuple `g` over `L`, and zero elsewhere.
  set G : ℂ → F := fun z ↦ ∑ j,
    Wkp.value k ((g : Fin (finrank ℝ F) → Wkp volume (A.halfImage i) p k) j) z • finBasis ℝ F j
  set s : ∀ x, V x := A.chartSection i fun y ↦
    if (A.chart i).symm y ∈ L then G (y : ℂ) else 0
  have hsL (x : M) (hx : x ∉ L) : s x = 0 := chartSection_eq_zero fun hxi ↦ by
    simp [(A.chart i).left_inv (A.dom_subset_chart_source i hxi), hx]
  have hsi {z : ℂ} (hz : z ∈ A.halfImage i) : A.halfCoord i s z =
      if (A.chart i).symm (closedUpperHalfPlaneModel.symm z) ∈ L then G z else 0 := by
    obtain ⟨hzi, hz0⟩ := A.mem_halfImage.1 hz
    rw [halfCoord_def, coord_chartSection _ hzi,
      coe_closedUpperHalfPlaneModel_symm_of_im_nonneg hz0.le]
  have hv (m : Fin (finrank ℝ F)) :
      (Wkp.value k ((g : Fin (finrank ℝ F) → Wkp volume (A.halfImage i) p k) m) : ℂ → ℝ)
      =ᵐ[volume.restrict (A.halfImage i : Set ℂ)]
        fun z ↦ (finBasis ℝ F).coord m (A.halfCoord i s z) := by
    filter_upwards [mem_chartAeZeroOff.1 g.property m,
      ae_restrict_mem (A.halfImage i).isOpen.measurableSet] with z h0 hz
    rw [hsi hz]
    split_ifs with hL'
    · rw [Basis.coord_apply, (finBasis ℝ F).repr_sum_self]
    · rw [h0 hL', map_zero]
  obtain ⟨w, hw⟩ :=
    exists_chartValueL_ae_eq_halfCoord_of_eq_zero hn hkn hL hLi hsL fun m ↦ ⟨_, hv m⟩
  refine ⟨⟨w, mem_aeZeroOff_of_ae_eq_halfCoord hw hsL⟩, Subtype.ext (funext fun m ↦ ?_)⟩
  rw [coe_chartRestrictL_apply]
  exact Wkp.ext k (Lp.ext ((value_ae_eq_repr_halfCoord (hw i) m).trans (hv m).symm))

section Extension

variable {n : ℕ} [IsManifold closedUpperHalfPlaneModel n M]
  [ContMDiffVectorBundle n F V closedUpperHalfPlaneModel]

variable (A p k) in
/-- For a `Cⁿ` bundle with `1 ≤ n` and `k ≤ n` and a closed subset `L` of the domain of chart `i`,
the chart-`i` components of the elements of `W^{k,p}(V)` vanishing off `L` form a linear
equivalence onto the chart-`i` tuples vanishing off `L`. -/
def chartRestrictEquiv (hn : 1 ≤ n) (hkn : k ≤ n) {i : Fin A.n} {L : Set M} (hL : IsClosed L)
    (hLi : L ⊆ A.dom i) : aeZeroOff A p k L ≃ₗ[ℝ] chartAeZeroOff A p k i L :=
  letI : IsManifold closedUpperHalfPlaneModel 1 M :=
    IsManifold.of_le (n := n) (by exact_mod_cast hn)
  A.halfSectionChartData.chartRestrictEquiv volume p k (chartRestrictL_injective hLi)
    (chartRestrictL_surjective hn hkn hL hLi)

@[simp]
theorem chartRestrictEquiv_apply (hn : 1 ≤ n) (hkn : k ≤ n) {i : Fin A.n} {L : Set M}
    (hL : IsClosed L) (hLi : L ⊆ A.dom i) (w : aeZeroOff A p k L) :
    chartRestrictEquiv A p k hn hkn hL hLi w = chartRestrictL A p k i L w :=
  letI : IsManifold closedUpperHalfPlaneModel 1 M :=
    IsManifold.of_le (n := n) (by exact_mod_cast hn)
  SectionChartData.chartRestrictEquiv_apply (chartRestrictL_injective hLi)
    (chartRestrictL_surjective hn hkn hL hLi) w

/-- **Extension by zero.** Let `L` be a closed subset of the domain of chart `i`, for a `Cⁿ` bundle
with `1 ≤ n` and `k ≤ n`. A tuple of chart-`i` Sobolev functions vanishing almost everywhere off
`L` defines an element of `W^{k,p}(V)`, vanishing off `L`, whose chart-`i` components are the given
functions. This is a continuous linear map from the closed subspace
`TauCeti.BorderedSobolevSection.chartAeZeroOff A p k i L` into `W^{k,p}(V)`
(`TauCeti.SectionChartData.extendByZeroL`). -/
def extendByZeroL (hn : 1 ≤ n) (hkn : k ≤ n) {i : Fin A.n} {L : Set M} (hL : IsClosed L)
    (hLi : L ⊆ A.dom i) : chartAeZeroOff A p k i L →L[ℝ] BorderedSobolevSection A p k :=
  letI : IsManifold closedUpperHalfPlaneModel 1 M :=
    IsManifold.of_le (n := n) (by exact_mod_cast hn)
  A.halfSectionChartData.extendByZeroL volume p k (chartRestrictL_injective hLi)
    (chartRestrictL_surjective hn hkn hL hLi)

theorem extendByZeroL_apply (hn : 1 ≤ n) (hkn : k ≤ n) {i : Fin A.n} {L : Set M}
    (hL : IsClosed L) (hLi : L ⊆ A.dom i) (g : chartAeZeroOff A p k i L) :
    extendByZeroL hn hkn hL hLi g = (chartRestrictEquiv A p k hn hkn hL hLi).symm g :=
  letI : IsManifold closedUpperHalfPlaneModel 1 M :=
    IsManifold.of_le (n := n) (by exact_mod_cast hn)
  SectionChartData.extendByZeroL_apply (chartRestrictL_injective hLi)
    (chartRestrictL_surjective hn hkn hL hLi) g

/-- The extension by zero vanishes off `L`. -/
theorem extendByZeroL_mem_aeZeroOff (hn : 1 ≤ n) (hkn : k ≤ n) {i : Fin A.n} {L : Set M}
    (hL : IsClosed L) (hLi : L ⊆ A.dom i) (g : chartAeZeroOff A p k i L) :
    extendByZeroL hn hkn hL hLi g ∈ aeZeroOff A p k L :=
  letI : IsManifold closedUpperHalfPlaneModel 1 M :=
    IsManifold.of_le (n := n) (by exact_mod_cast hn)
  SectionChartData.extendByZeroL_mem_aeZeroOn (chartRestrictL_injective hLi)
    (chartRestrictL_surjective hn hkn hL hLi) g

/-- The chart-`i` components of the extension by zero are the given tuple. -/
@[simp]
theorem chartRestrictL_extendByZeroL (hn : 1 ≤ n) (hkn : k ≤ n) {i : Fin A.n} {L : Set M}
    (hL : IsClosed L) (hLi : L ⊆ A.dom i) (g : chartAeZeroOff A p k i L) :
    chartRestrictL A p k i L ⟨_, extendByZeroL_mem_aeZeroOff hn hkn hL hLi g⟩ = g :=
  letI : IsManifold closedUpperHalfPlaneModel 1 M :=
    IsManifold.of_le (n := n) (by exact_mod_cast hn)
  SectionChartData.chartRestrictL_extendByZeroL (chartRestrictL_injective hLi)
    (chartRestrictL_surjective hn hkn hL hLi) g

/-- The chart-`i` components of the extension by zero are the given functions. -/
@[simp]
theorem extendByZeroL_apply_self (hn : 1 ≤ n) (hkn : k ≤ n) {i : Fin A.n} {L : Set M}
    (hL : IsClosed L) (hLi : L ⊆ A.dom i) (g : chartAeZeroOff A p k i L) :
    ((extendByZeroL hn hkn hL hLi g : BorderedSobolevSection A p k) :
      A.halfSectionChartData.SobolevData volume p k) i =
      (g : Fin (finrank ℝ F) → Wkp volume (A.halfImage i) p k) :=
  letI : IsManifold closedUpperHalfPlaneModel 1 M :=
    IsManifold.of_le (n := n) (by exact_mod_cast hn)
  SectionChartData.extendByZeroL_apply_self (chartRestrictL_injective hLi)
    (chartRestrictL_surjective hn hkn hL hLi) g

/-- An element vanishing off `L` is the extension by zero of its chart-`i` components. -/
@[simp]
theorem extendByZeroL_chartRestrictL (hn : 1 ≤ n) (hkn : k ≤ n) {i : Fin A.n} {L : Set M}
    (hL : IsClosed L) (hLi : L ⊆ A.dom i) (w : aeZeroOff A p k L) :
    extendByZeroL hn hkn hL hLi (chartRestrictL A p k i L w) = w :=
  letI : IsManifold closedUpperHalfPlaneModel 1 M :=
    IsManifold.of_le (n := n) (by exact_mod_cast hn)
  SectionChartData.extendByZeroL_chartRestrictL (chartRestrictL_injective hLi)
    (chartRestrictL_surjective hn hkn hL hLi) w

/-- Elements vanishing off `L` converge as soon as their chart-`i` components converge, since
extension by zero is continuous. -/
theorem tendsto_of_tendsto_chartRestrictL (hn : 1 ≤ n) (hkn : k ≤ n) {i : Fin A.n} {L : Set M}
    (hL : IsClosed L) (hLi : L ⊆ A.dom i) {ι : Type*} {l : Filter ι} {a : ι → aeZeroOff A p k L}
    {u : aeZeroOff A p k L}
    (h : Tendsto (fun m ↦ chartRestrictL A p k i L (a m)) l (𝓝 (chartRestrictL A p k i L u))) :
    Tendsto a l (𝓝 u) := by
  have hE := ((extendByZeroL hn hkn hL hLi).continuous.tendsto _).comp h
  simp only [Function.comp_def, extendByZeroL_chartRestrictL] at hE
  exact tendsto_subtype_rng.2 hE

end Extension

end BorderedSobolevSection

end TauCeti
