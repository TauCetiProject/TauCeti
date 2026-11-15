/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Morrey.HalfDisc
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Bordered.Basic

/-!
# Morrey's embedding for Sobolev sections over surfaces with boundary

Let `M` be a `C¹` manifold modelled on the closed upper half-plane `ClosedUpperHalfPlane`, for
instance a surface with boundary, let `V → M` be a real vector bundle with finite-dimensional model
fibre `F`, let `A` be a finite bundle atlas and let `2 < p ≤ ∞`. This file proves that every element
`w` of the Sobolev space `W^{1,p}(V)` of `TauCeti.BorderedSobolevSection A p 1` has a unique
continuous representative: there is exactly one continuous section `s` of `V` whose coordinates in
every chart `i` of `A` agree almost everywhere on the interior `A.halfImage i` of the chart image
with the chart data of `w`
(`TauCeti.BorderedSobolevSection.existsUnique_continuous_ae_eq_halfCoord`). It is
`TauCeti.BorderedSobolevSection.toSection`, and its chart expressions are Hölder continuous with
exponent `1 - 2 / p` on compact subsets of the chart images, which may meet the real axis
(`TauCeti.BorderedSobolevSection.exists_holderOnWith_halfCoord_toSection`). In particular every
element of `W^{1,p}(V)` has well-defined values at the boundary points of `M`.

The proof is local and follows the boundaryless case `TauCeti.SobolevSection.toSection`. An element
`w` consists of the components of some section `s`, defined only up to null sets, whose chart
expression `A.halfCoord i s` lies in `MemWkpLoc p (A.halfClosedImage i) 1`
(`TauCeti.BorderedSobolevSection.memWkpLoc_halfCoord`). By Morrey's embedding up to the real axis
its representative `gᵢ = TauCeti.halfPlanePreciseRepresentative (A.halfCoord i s)` is continuous on
the chart image `A.halfClosedImage i`, real-axis points included, and agrees with `A.halfCoord i s`
almost everywhere there. The coordinates of `s` in two charts are related by the coordinate change
of the bundle; since chart transitions preserve null sets, the representatives `gᵢ` satisfy the
same relation almost everywhere on the interiors of the overlaps, hence everywhere there by
continuity, and then also at the points of the overlaps on the real axis, which are limits of
interior points. Therefore the `gᵢ` glue to a continuous section
(`TauCeti.FiniteBundleAtlas.exists_continuous_halfCoord_eqOn`). Uniqueness holds because two
continuous sections whose chart expressions agree almost everywhere on the interiors of the chart
images are equal (`TauCeti.FiniteBundleAtlas.eq_of_continuous_of_halfCoord_ae_eq`).

## Main results

* `TauCeti.BorderedSobolevSection.existsUnique_continuous_ae_eq_halfCoord`: an element of
  `W^{1,p}(V)`, for `p > 2`, has a unique continuous representative.
* `TauCeti.BorderedSobolevSection.toSection`: that continuous section; it is linear in the element
  of `W^{1,p}(V)`, and `TauCeti.BorderedSobolevSection.toSectionₗ` packages it as a real-linear map.
* `TauCeti.BorderedSobolevSection.toSection_injective`: distinct elements have distinct continuous
  representatives, and `TauCeti.BorderedSobolevSection.toSection_ofContMDiffSection`: a `C¹`
  section is its own continuous representative.
* `TauCeti.BorderedSobolevSection.exists_holderOnWith_halfCoord_toSection`: its chart expressions
  are `(1 - 2 / p)`-Hölder on compact subsets of the chart images, up to the real axis.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 (Sobolev spaces of sections and the Sobolev embedding theorem).
* R. S. Palais, *Foundations of Global Non-linear Analysis*, Benjamin (1968), §9.
-/

public section

noncomputable section

open Bundle MeasureTheory Module Set TopologicalSpace TauCeti.MeasureTheory
open scoped Manifold ENNReal NNReal

namespace TauCeti

section Atlas

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ClosedUpperHalfPlane M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V]

namespace FiniteBundleAtlas

variable (A : FiniteBundleAtlas ClosedUpperHalfPlane M F V)

/-- Morrey's embedding up to the real axis, on the image of chart `i`. -/
private theorem continuousOn_halfPlanePreciseRepresentative [FiniteDimensional ℝ F] {p : ℝ≥0∞}
    (hp : 2 < p) {i : Fin A.n} {u : ℂ → F} (hu : MemWkpLoc p (A.halfClosedImage i) 1 u) :
    ContinuousOn (halfPlanePreciseRepresentative u) (A.halfClosedImage i) := by
  rw [A.halfClosedImage_eq_inter] at hu ⊢
  exact hu.continuousOn_halfPlanePreciseRepresentative hp

/-- The representative up to the real axis agrees with `u` almost everywhere on the interior of the
image of chart `i`. -/
private theorem ae_eq_halfPlanePreciseRepresentative [FiniteDimensional ℝ F] {p : ℝ≥0∞}
    [Fact (1 ≤ p)] {i : Fin A.n} {u : ℂ → F}
    (hu : MemWkpLoc p (A.halfClosedImage i) 1 u) :
    u =ᵐ[volume.restrict (A.halfImage i : Set ℂ)] halfPlanePreciseRepresentative u := by
  rw [A.halfClosedImage_eq_inter] at hu
  have h := hu.ae_eq_halfPlanePreciseRepresentative Fact.out
  rw [← A.halfClosedImage_eq_inter] at h
  exact ae_restrict_of_ae_restrict_of_subset (A.halfImage_subset_halfClosedImage i) h

end FiniteBundleAtlas

end Atlas

section Morrey

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ClosedUpperHalfPlane M]
  [IsManifold closedUpperHalfPlaneModel 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  {A : FiniteBundleAtlas ClosedUpperHalfPlane M F V} {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace BorderedSobolevSection

open FiniteBundleAtlas

/-- The representatives constructed in the proof of
`TauCeti.BorderedSobolevSection.existsUnique_continuous_ae_eq_halfCoord`: given a section `s` whose
chart expressions are in `MemWkpLoc p (A.halfClosedImage i) 1`, their representatives up to the
real axis are the chart expressions of a continuous section on the chart images. -/
private theorem exists_continuous_eqOn_halfPlanePreciseRepresentative (hp : 2 < p)
    {s : ∀ x, V x} (hs : ∀ i, MemWkpLoc p (A.halfClosedImage i) 1 (A.halfCoord i s)) :
    ∃ t : ∀ x, V x, Continuous (fun x ↦ TotalSpace.mk' F x (t x)) ∧
      ∀ i, EqOn (A.halfCoord i t) (halfPlanePreciseRepresentative (A.halfCoord i s))
        (A.halfClosedImage i) := by
  set g : Fin A.n → ℂ → F := fun i ↦ halfPlanePreciseRepresentative (A.halfCoord i s)
  have hg_cont (i : Fin A.n) : ContinuousOn (g i) (A.halfClosedImage i) :=
    A.continuousOn_halfPlanePreciseRepresentative hp (hs i)
  have hg_ae (i : Fin A.n) : A.halfCoord i s =ᵐ[volume.restrict (A.halfImage i : Set ℂ)] g i :=
    A.ae_eq_halfPlanePreciseRepresentative (hs i)
  -- The representatives satisfy the cocycle relation at every interior point of every overlap.
  have hcompat (i i' : Fin A.n) : EqOn (g i')
      (fun z ↦ (A.triv i).coordChangeL ℝ (A.triv i')
        ((A.chart i').symm (closedUpperHalfPlaneModel.symm z)) (g i (A.halfTransition i i' z)))
      (A.halfOverlap i i') := by
    refine Measure.eqOn_open_of_ae_eq (μ := volume) ?_ (A.isOpen_halfOverlap i i')
      ((hg_cont i').mono ((A.halfOverlap_subset_halfImage i i').trans
        (A.halfImage_subset_halfClosedImage i')))
      ((A.continuousOn_coordChange_halfTransition (hg_cont i)).mono fun _ hz ↦
        (A.mem_halfOverlap.1 hz).1)
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (A.halfOverlap_subset_halfImage i i')
        (hg_ae i'), A.halfSectionChartData.aeTransition_iff.1
          A.aeTransition_halfSectionChartData (i' := i') (hg_ae i),
        ae_restrict_mem (A.isOpen_halfOverlap i i').measurableSet] with z h' h hz
    rw [A.halfSectionChartData_transition_of_mem hz] at h
    rw [← h', ← h, A.halfCoord_eq_coordChange s hz]
  exact A.exists_continuous_halfCoord_eqOn hg_cont hcompat

/-- **Morrey's embedding for Sobolev sections over surfaces with boundary: continuous
representatives.** For `2 < p ≤ ∞`, every element `w` of `W^{1,p}(V)` has exactly one continuous
representative: there is a unique continuous section `s` of `V` whose chart expression
`A.halfCoord i s` agrees, for every chart `i`, almost everywhere on the interior `A.halfImage i` of
the chart image with the chart data of `w`. -/
theorem existsUnique_continuous_ae_eq_halfCoord (hp : 2 < p)
    (w : BorderedSobolevSection A p 1) :
    ∃! s : ∀ x, V x, Continuous (fun x ↦ TotalSpace.mk' F x (s x)) ∧
      ∀ i, A.halfSectionChartData.chartValueL volume p 1 i w
        =ᵐ[volume.restrict (A.halfImage i : Set ℂ)] A.halfCoord i s := by
  obtain ⟨s, hs, hmem⟩ := exists_section_memWkpLoc w
  obtain ⟨t, ht, hts⟩ := exists_continuous_eqOn_halfPlanePreciseRepresentative hp hmem
  have hae (i : Fin A.n) :
      A.halfSectionChartData.chartValueL volume p 1 i w
        =ᵐ[volume.restrict (A.halfImage i : Set ℂ)] A.halfCoord i t := by
    filter_upwards [hs i, A.ae_eq_halfPlanePreciseRepresentative (hmem i),
      ae_restrict_mem (A.halfImage i).isOpen.measurableSet] with z hz hz' hzU
    rw [hz, hz', hts i (A.halfImage_subset_halfClosedImage i hzU)]
  exact ⟨t, ⟨ht, hae⟩, fun t' ht' ↦ A.eq_of_continuous_of_halfCoord_ae_eq (μ := volume) ht'.1 ht
    fun i ↦ (ht'.2 i).symm.trans (hae i)⟩

/-- The continuous representative of an element of `W^{1,p}(V)`, for `2 < p ≤ ∞`: the unique
continuous section whose chart expressions agree almost everywhere with the chart data
(`TauCeti.BorderedSobolevSection.existsUnique_continuous_ae_eq_halfCoord`). Its values at the
boundary points of `M` are the boundary values of the element. -/
def toSection (hp : 2 < p) (w : BorderedSobolevSection A p 1) : ∀ x, V x :=
  (existsUnique_continuous_ae_eq_halfCoord hp w).exists.choose

/-- The continuous representative is a continuous section. -/
theorem continuous_toSection (hp : 2 < p) (w : BorderedSobolevSection A p 1) :
    Continuous fun x ↦ TotalSpace.mk' F x (toSection hp w x) :=
  (existsUnique_continuous_ae_eq_halfCoord hp w).exists.choose_spec.1

/-- The chart data of an element of `W^{1,p}(V)` are the chart expressions of its continuous
representative, almost everywhere. -/
theorem chartValueL_ae_eq_halfCoord_toSection (hp : 2 < p) (w : BorderedSobolevSection A p 1)
    (i : Fin A.n) :
    A.halfSectionChartData.chartValueL volume p 1 i w
      =ᵐ[volume.restrict (A.halfImage i : Set ℂ)] A.halfCoord i (toSection hp w) :=
  (existsUnique_continuous_ae_eq_halfCoord hp w).exists.choose_spec.2 i

/-- **Uniqueness of the continuous representative.** A continuous section whose chart
expressions agree almost everywhere with the chart data of `w` is the continuous representative
of `w`. -/
theorem eq_toSection (hp : 2 < p) {w : BorderedSobolevSection A p 1} {s : ∀ x, V x}
    (hs : Continuous fun x ↦ TotalSpace.mk' F x (s x))
    (hw : ∀ i, A.halfSectionChartData.chartValueL volume p 1 i w
      =ᵐ[volume.restrict (A.halfImage i : Set ℂ)] A.halfCoord i s) :
    s = toSection hp w :=
  (existsUnique_continuous_ae_eq_halfCoord hp w).unique ⟨hs, hw⟩
    ⟨continuous_toSection hp w, chartValueL_ae_eq_halfCoord_toSection hp w⟩

/-- The chart data of an element of `W^{1,p}(V)` are, almost everywhere, the readings of its
continuous representative in the chart data `A.halfSectionChartData`. -/
private theorem chartValueL_ae_eq_coord_toSection (hp : 2 < p) (w : BorderedSobolevSection A p 1)
    (i : Fin A.n) :
    A.halfSectionChartData.chartValueL volume p 1 i w
      =ᵐ[volume.restrict (A.halfImage i : Set ℂ)]
        A.halfSectionChartData.coord i (toSection hp w) :=
  (chartValueL_ae_eq_halfCoord_toSection hp w i).trans
    (A.halfSectionChartData_coord_ae_eq i _).symm

/-- **Injectivity.** Distinct elements of `W^{1,p}(V)` have distinct continuous
representatives. -/
theorem toSection_injective (hp : 2 < p) :
    Function.Injective (toSection hp : BorderedSobolevSection A p 1 → ∀ x, V x) :=
  fun w w' h ↦ SectionChartData.eq_of_ae_eq_coord (chartValueL_ae_eq_coord_toSection hp w)
    (h ▸ chartValueL_ae_eq_coord_toSection hp w')

/-- The continuous representative of a `C¹` section, viewed as an element of `W^{1,p}(V)`, is the
section itself. The smoothness instances are stated at `(1 : ℕ)`, as in
`TauCeti.BorderedSobolevSection.ofContMDiffSection`. -/
@[simp]
theorem toSection_ofContMDiffSection [IsManifold closedUpperHalfPlaneModel (1 : ℕ) M]
    [ContMDiffVectorBundle (1 : ℕ) F V closedUpperHalfPlaneModel] (hp : 2 < p)
    (s : Cₛ^(1 : ℕ)⟮closedUpperHalfPlaneModel; F, V⟯) :
    toSection hp (ofContMDiffSection A p 1 s) = s :=
  (eq_toSection hp s.contMDiff.continuous (chartValueL_ofContMDiffSection_ae A p 1 s)).symm

/-- Taking continuous representatives is additive. -/
@[simp]
theorem toSection_add (hp : 2 < p) (w v : BorderedSobolevSection A p 1) :
    toSection hp (w + v) = toSection hp w + toSection hp v := by
  refine (eq_toSection hp ?_ fun (i : Fin A.n) ↦ ?_).symm
  · exact contMDiff_zero_iff.1 (ContMDiff.add_section (I := closedUpperHalfPlaneModel)
      (contMDiff_zero_iff.2 (continuous_toSection hp w))
      (contMDiff_zero_iff.2 (continuous_toSection hp v)))
  · filter_upwards [Lp.coeFn_add (A.halfSectionChartData.chartValueL volume p 1 i w)
        (A.halfSectionChartData.chartValueL volume p 1 i v),
      chartValueL_ae_eq_coord_toSection hp w i, chartValueL_ae_eq_coord_toSection hp v i,
      ae_restrict_mem (A.halfImage i).isOpen.measurableSet] with z hz hw hv hzU
    rw [AddMemClass.coe_add, map_add, hz, Pi.add_apply, hw, hv,
      ← A.halfSectionChartData.coord_add i _ _ z hzU, A.halfSectionChartData_coord_of_mem _ hzU]

/-- Taking continuous representatives commutes with real scalar multiplication. -/
@[simp]
theorem toSection_smul (hp : 2 < p) (c : ℝ) (w : BorderedSobolevSection A p 1) :
    toSection hp (c • w) = c • toSection hp w := by
  refine (eq_toSection hp ?_ fun (i : Fin A.n) ↦ ?_).symm
  · exact contMDiff_zero_iff.1 (ContMDiff.const_smul_section (I := closedUpperHalfPlaneModel)
      (a := c) (contMDiff_zero_iff.2 (continuous_toSection hp w)))
  · filter_upwards [Lp.coeFn_smul c (A.halfSectionChartData.chartValueL volume p 1 i w),
      chartValueL_ae_eq_coord_toSection hp w i,
      ae_restrict_mem (A.halfImage i).isOpen.measurableSet] with z hz hw hzU
    rw [SetLike.val_smul, map_smul, hz, Pi.smul_apply, hw,
      ← A.halfSectionChartData.coord_smul i _ _ z hzU, A.halfSectionChartData_coord_of_mem _ hzU]

/-- Taking continuous representatives, as a real-linear map from `W^{1,p}(V)` to sections. -/
def toSectionₗ (hp : 2 < p) : BorderedSobolevSection A p 1 →ₗ[ℝ] ∀ x, V x where
  toFun := toSection hp
  map_add' := toSection_add hp
  map_smul' := toSection_smul hp

@[simp]
theorem toSectionₗ_apply (hp : 2 < p) (w : BorderedSobolevSection A p 1) :
    toSectionₗ hp w = toSection hp w :=
  (rfl)

/-- The continuous representative of `0` is the zero section. -/
@[simp]
theorem toSection_zero (hp : 2 < p) : toSection hp (0 : BorderedSobolevSection A p 1) = 0 :=
  map_zero (toSectionₗ hp)

/-- Taking continuous representatives commutes with negation. -/
@[simp]
theorem toSection_neg (hp : 2 < p) (w : BorderedSobolevSection A p 1) :
    toSection hp (-w) = -toSection hp w :=
  map_neg (toSectionₗ hp) w

/-- Taking continuous representatives commutes with subtraction. -/
@[simp]
theorem toSection_sub (hp : 2 < p) (w v : BorderedSobolevSection A p 1) :
    toSection hp (w - v) = toSection hp w - toSection hp v :=
  map_sub (toSectionₗ hp) w v

/-- The chart expressions of the continuous representative are, on the chart images and including
their points on the real axis, the representatives `TauCeti.halfPlanePreciseRepresentative` of the
chart expressions of any section whose coordinates are the chart data. -/
theorem eqOn_halfCoord_toSection (hp : 2 < p) {w : BorderedSobolevSection A p 1} {s : ∀ x, V x}
    (hs : ∀ i, A.halfSectionChartData.chartValueL volume p 1 i w
      =ᵐ[volume.restrict (A.halfImage i : Set ℂ)] A.halfCoord i s)
    (i : Fin A.n) :
    EqOn (A.halfCoord i (toSection hp w)) (halfPlanePreciseRepresentative (A.halfCoord i s))
      (A.halfClosedImage i) := by
  have hu := memWkpLoc_halfCoord w hs i
  have hc := A.continuousOn_halfCoord (continuous_toSection hp w) i
  have hc' := A.continuousOn_halfPlanePreciseRepresentative hp hu
  have hsub := A.halfImage_subset_halfClosedImage i
  exact (Measure.eqOn_open_of_ae_eq ((chartValueL_ae_eq_halfCoord_toSection hp w i).symm.trans
    ((hs i).trans (A.ae_eq_halfPlanePreciseRepresentative hu))) (A.halfImage i).isOpen
      (hc.mono hsub) (hc'.mono hsub)).of_subset_closure hc hc' hsub
        (A.halfClosedImage_subset_closure_halfImage i)

/-- **Morrey's embedding for Sobolev sections over surfaces with boundary: Hölder continuity in
charts.** For `2 < p ≤ ∞`, the chart expression of the continuous representative of an element of
`W^{1,p}(V)` is Hölder continuous with exponent `1 - 2 / p` on every compact subset of the chart
image, which may contain points of the real axis. -/
theorem exists_holderOnWith_halfCoord_toSection (hp : 2 < p) (w : BorderedSobolevSection A p 1)
    (i : Fin A.n) {K : Set ℂ} (hK : IsCompact K) (hKi : K ⊆ A.halfClosedImage i) :
    ∃ C : ℝ≥0, HolderOnWith C ((1 : ℝ≥0∞) - 2 / p).toNNReal
      (A.halfCoord i (toSection hp w)) K := by
  obtain ⟨s, hs, hmem⟩ := exists_section_memWkpLoc w
  have hu := hmem i
  rw [A.halfClosedImage_eq_inter] at hu
  obtain ⟨C, hC⟩ := hu.exists_holderOnWith_halfPlanePreciseRepresentative_of_isCompact hp hK
    (hKi.trans (A.halfClosedImage_eq_inter i).subset)
  refine ⟨C, fun x hx y hy ↦ ?_⟩
  rw [eqOn_halfCoord_toSection hp hs i (hKi hx), eqOn_halfCoord_toSection hp hs i (hKi hy)]
  exact hC x hx y hy

end BorderedSobolevSection

end Morrey

end TauCeti
