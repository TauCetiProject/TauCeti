/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Morrey
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.AEEq
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.ContMDiffSection
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Local

/-!
# Morrey's embedding for Sobolev sections over surfaces

Let `M` be a manifold without boundary modelled on `ℂ`, let `V → M` be a real vector bundle with
finite-dimensional model fibre `F`, let `A` be a finite bundle atlas and let `2 < p ≤ ∞`. This file
proves that every element `w` of the Sobolev space `W^{1,p}(V)` of
`TauCeti.SobolevSection A volume p 1` has a unique continuous representative: there is exactly one
continuous section `s` of `V` whose coordinates in every chart `i` of `A` agree almost everywhere
on `A.image i` with the chart data of `w`
(`TauCeti.SobolevSection.existsUnique_continuous_ae_eq_coord`). It is
`TauCeti.SobolevSection.toSection`, and its chart expressions are Hölder continuous with exponent
`1 - 2 / p` on compact subsets of the chart images
(`TauCeti.SobolevSection.exists_holderOnWith_coord_toSection`).

The proof is local. An element `w` consists of the components of some section `s`, defined only up
to null sets, whose chart expression `A.coord i s` lies in `MemWkpLoc p (A.image i) 1`
(`TauCeti.SobolevSection.memWkpLoc_coord`). By the planar Morrey embedding its precise
representative `gᵢ` is continuous on `A.image i`
(`TauCeti.MemWkpLoc.continuousOn_preciseRepresentative`) and agrees with `A.coord i s` almost
everywhere there. The coordinates of `s` in two charts are related by the coordinate change of the
bundle at every point of the overlap; since chart transitions preserve null sets, the
representatives `gᵢ` satisfy the same relation almost everywhere, and hence everywhere, both sides
being continuous on the open overlap and Lebesgue measure charging every nonempty open set.
Therefore the representatives `gᵢ` glue to a continuous section with chart expression `gᵢ` on
`A.image i` for every chart `i` (`TauCeti.FiniteBundleAtlas.exists_continuous_coord_eqOn`).
Uniqueness holds because two continuous sections whose chart expressions agree almost everywhere
agree everywhere (`TauCeti.FiniteBundleAtlas.eq_of_continuous_of_coord_ae_eq`).

The hypothesis `2 < p` cannot be dropped: in dimension two the space `W^{1,2}` contains unbounded
functions.

## Main results

* `TauCeti.SobolevSection.existsUnique_continuous_ae_eq_coord`: an element of `W^{1,p}(V)`, for
  `p > 2`, has a unique continuous representative.
* `TauCeti.SobolevSection.toSection`: that continuous section; it is linear in the element of
  `W^{1,p}(V)`, and `TauCeti.SobolevSection.toSectionₗ` packages it as a real-linear map.
* `TauCeti.SobolevSection.toSection_injective`: distinct elements have distinct continuous
  representatives, and `TauCeti.SobolevSection.toSection_ofContMDiffSection`: a `C¹` section is
  its own continuous representative.
* `TauCeti.SobolevSection.exists_holderOnWith_coord_toSection`: its chart expressions are
  `(1 - 2 / p)`-Hölder on compact subsets of the chart images.

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

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℝ, ℂ) 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  {A : FiniteBundleAtlas ℂ M F V} {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace SobolevSection

open FiniteBundleAtlas

/-- The representatives constructed in the proof of
`TauCeti.SobolevSection.existsUnique_continuous_ae_eq_coord`: given a section `s` whose chart
expressions are in `MemWkpLoc p (A.image i) 1`, the precise representatives of its chart
expressions are the chart expressions of a continuous section on the chart images. -/
private theorem exists_continuous_eqOn_preciseRepresentative (hp : 2 < p) {s : ∀ x, V x}
    (hs : ∀ i, MemWkpLoc p (A.image i) 1 (A.coord i s)) :
    ∃ t : ∀ x, V x, Continuous (fun x ↦ TotalSpace.mk' F x (t x)) ∧
      ∀ i, EqOn (A.coord i t) (preciseRepresentative volume (A.coord i s)) (A.image i) := by
  set g : Fin A.n → ℂ → F := fun i ↦ preciseRepresentative volume (A.coord i s)
  have hg_cont (i : Fin A.n) : ContinuousOn (g i) (A.image i) :=
    (hs i).continuousOn_preciseRepresentative hp
  have hg_ae (i : Fin A.n) : A.coord i s =ᵐ[volume.restrict (A.image i)] g i :=
    (hs i).memLpLoc.ae_eq_preciseRepresentative Fact.out
  -- The chart transitions and the base points of the overlaps.
  have hsymm (i i' : Fin A.n) {y : ℂ} (hy : y ∈ A.overlap i i') :
      (A.chart i').symm y ∈ A.dom i ∩ A.dom i' := by
    obtain ⟨x, hx, rfl⟩ := A.mem_overlap.1 hy
    rwa [(A.chart i').left_inv (A.dom_subset_chart_source i' hx.2)]
  have htrans (i i' : Fin A.n) : ContinuousOn (A.transition i i') (A.overlap i i') :=
    (A.differentiableOn_transition i i').continuousOn
  -- The representatives satisfy the cocycle relation at every point of every overlap.
  have hcompat (i i' : Fin A.n) : EqOn (g i')
      (fun y ↦ (A.triv i).coordChangeL ℝ (A.triv i') ((A.chart i').symm y)
        (g i (A.transition i i' y))) (A.overlap i i') := by
    refine Measure.eqOn_open_of_ae_eq (μ := volume) ?_ (A.isOpen_overlap i i')
      ((hg_cont i').mono (A.overlap_subset_image i i')) ?_
    · filter_upwards [ae_restrict_of_ae_restrict_of_subset (A.overlap_subset_image i i')
        (hg_ae i'), A.sectionChartData.aeTransition_iff.1 (A.aeTransition_sectionChartData volume)
          (i' := i') (hg_ae i),
        ae_restrict_mem (A.isOpen_overlap i i').measurableSet] with y h' h hy
      rw [A.sectionChartData_transition_of_mem hy] at h
      rw [← h', ← h, A.coord_eq_coordChange s hy]
    · have hbase : MapsTo (A.chart i').symm (A.overlap i i')
          ((A.triv i).baseSet ∩ (A.triv i').baseSet) := fun y hy ↦
        ⟨A.dom_subset_baseSet i (hsymm i i' hy).1, A.dom_subset_baseSet i' (hsymm i i' hy).2⟩
      exact ((continuousOn_coordChange ℝ (A.triv i) (A.triv i')).comp
        ((A.continuousOn_chart_symm i').mono (A.overlap_subset_image i i')) hbase).clm_apply
        ((hg_cont i).comp (htrans i i') fun y hy ↦
          A.overlap_subset_image i' i (A.transition_mem_overlap hy))
  exact A.exists_continuous_coord_eqOn hg_cont hcompat

/-- **Morrey's embedding for Sobolev sections: continuous representatives.** For `2 < p ≤ ∞`,
every element `w` of `W^{1,p}(V)` has exactly one continuous representative: there is a unique
continuous section `s` of `V` whose chart expression `A.coord i s` agrees, for every chart `i`,
almost everywhere on `A.image i` with the chart data of `w`. -/
theorem existsUnique_continuous_ae_eq_coord (hp : 2 < p) (w : SobolevSection A volume p 1) :
    ∃! s : ∀ x, V x, Continuous (fun x ↦ TotalSpace.mk' F x (s x)) ∧
      ∀ i, A.sectionChartData.chartValueL volume p 1 i w
        =ᵐ[volume.restrict (A.image i)] A.coord i s := by
  obtain ⟨s, hs⟩ := A.sectionChartData.exists_section volume p 1 w
  replace hs (i : Fin A.n) := (hs i).trans (A.sectionChartData_coord_ae_eq volume i s)
  obtain ⟨t, ht, hts⟩ :=
    exists_continuous_eqOn_preciseRepresentative hp fun i ↦ memWkpLoc_coord w hs i
  have hae (i : Fin A.n) :
      A.sectionChartData.chartValueL volume p 1 i w
        =ᵐ[volume.restrict (A.image i)] A.coord i t := by
    filter_upwards [hs i, (memWkpLoc_coord w hs i).memLpLoc.ae_eq_preciseRepresentative Fact.out,
      ae_restrict_mem (A.image i).isOpen.measurableSet] with y hy hy' hyU
    rw [hy, hy', hts i hyU]
  exact ⟨t, ⟨ht, hae⟩, fun t' ht' ↦ A.eq_of_continuous_of_coord_ae_eq (μ := volume) ht'.1 ht
    fun i ↦ (ht'.2 i).symm.trans (hae i)⟩

/-- The continuous representative of an element of `W^{1,p}(V)`, for `2 < p ≤ ∞`: the unique
continuous section whose chart expressions agree almost everywhere with the chart data
(`TauCeti.SobolevSection.existsUnique_continuous_ae_eq_coord`). -/
def toSection (hp : 2 < p) (w : SobolevSection A volume p 1) : ∀ x, V x :=
  (existsUnique_continuous_ae_eq_coord hp w).exists.choose

/-- The continuous representative is a continuous section. -/
theorem continuous_toSection (hp : 2 < p) (w : SobolevSection A volume p 1) :
    Continuous fun x ↦ TotalSpace.mk' F x (toSection hp w x) :=
  (existsUnique_continuous_ae_eq_coord hp w).exists.choose_spec.1

/-- The chart data of an element of `W^{1,p}(V)` are the chart expressions of its continuous
representative, almost everywhere. -/
theorem chartValueL_ae_eq_coord_toSection (hp : 2 < p) (w : SobolevSection A volume p 1)
    (i : Fin A.n) :
    A.sectionChartData.chartValueL volume p 1 i w
      =ᵐ[volume.restrict (A.image i)] A.coord i (toSection hp w) :=
  (existsUnique_continuous_ae_eq_coord hp w).exists.choose_spec.2 i

/-- **Uniqueness of the continuous representative.** A continuous section whose chart
expressions agree almost everywhere with the chart data of `w` is the continuous representative
of `w`. -/
theorem eq_toSection (hp : 2 < p) {w : SobolevSection A volume p 1} {s : ∀ x, V x}
    (hs : Continuous fun x ↦ TotalSpace.mk' F x (s x))
    (hw : ∀ i, A.sectionChartData.chartValueL volume p 1 i w
      =ᵐ[volume.restrict (A.image i)] A.coord i s) :
    s = toSection hp w :=
  (existsUnique_continuous_ae_eq_coord hp w).unique ⟨hs, hw⟩
    ⟨continuous_toSection hp w, chartValueL_ae_eq_coord_toSection hp w⟩

/-- **Injectivity.** Distinct elements of `W^{1,p}(V)` have distinct continuous
representatives. -/
theorem toSection_injective (hp : 2 < p) :
    Function.Injective (toSection hp : SobolevSection A volume p 1 → ∀ x, V x) :=
  fun w w' h ↦ eq_of_ae_eq_coord (chartValueL_ae_eq_coord_toSection hp w)
    (h ▸ chartValueL_ae_eq_coord_toSection hp w')

/-- The continuous representative of a `C¹` section, viewed as an element of `W^{1,p}(V)`, is the
section itself. The smoothness instances are stated at `(1 : ℕ)`, as in
`TauCeti.SobolevSection.ofContMDiffSection`. -/
@[simp]
theorem toSection_ofContMDiffSection [IsManifold 𝓘(ℝ, ℂ) (1 : ℕ) M]
    [ContMDiffVectorBundle (1 : ℕ) F V 𝓘(ℝ, ℂ)] (hp : 2 < p) (s : Cₛ^(1 : ℕ)⟮𝓘(ℝ, ℂ); F, V⟯) :
    toSection hp (ofContMDiffSection A volume p 1 s) = s :=
  (eq_toSection hp s.contMDiff.continuous
    (chartValueL_ofContMDiffSection_ae A volume p 1 s)).symm

/-- Taking continuous representatives is additive. -/
@[simp]
theorem toSection_add (hp : 2 < p) (w v : SobolevSection A volume p 1) :
    toSection hp (w + v) = toSection hp w + toSection hp v := by
  refine (eq_toSection hp ?_ fun i ↦ ?_).symm
  · exact contMDiff_zero_iff.1 (ContMDiff.add_section (I := 𝓘(ℝ, ℂ))
      (contMDiff_zero_iff.2 (continuous_toSection hp w))
      (contMDiff_zero_iff.2 (continuous_toSection hp v)))
  · filter_upwards [Lp.coeFn_add (A.sectionChartData.chartValueL volume p 1 i w)
        (A.sectionChartData.chartValueL volume p 1 i v),
      chartValueL_ae_eq_coord_toSection hp w i, chartValueL_ae_eq_coord_toSection hp v i,
      ae_restrict_mem (A.image i).isOpen.measurableSet] with y hy hw hv hyU
    rw [AddMemClass.coe_add, map_add, hy, Pi.add_apply, hw, hv, A.coord_add i _ _ hyU]

/-- Taking continuous representatives commutes with real scalar multiplication. -/
@[simp]
theorem toSection_smul (hp : 2 < p) (c : ℝ) (w : SobolevSection A volume p 1) :
    toSection hp (c • w) = c • toSection hp w := by
  refine (eq_toSection hp ?_ fun i ↦ ?_).symm
  · exact contMDiff_zero_iff.1 (ContMDiff.const_smul_section (I := 𝓘(ℝ, ℂ)) (a := c)
      (contMDiff_zero_iff.2 (continuous_toSection hp w)))
  · filter_upwards [Lp.coeFn_smul c (A.sectionChartData.chartValueL volume p 1 i w),
      chartValueL_ae_eq_coord_toSection hp w i,
      ae_restrict_mem (A.image i).isOpen.measurableSet] with y hy hw hyU
    rw [SetLike.val_smul, map_smul, hy, Pi.smul_apply, hw, A.coord_smul i _ _ hyU]

/-- Taking continuous representatives, as a real-linear map from `W^{1,p}(V)` to sections. -/
def toSectionₗ (hp : 2 < p) : SobolevSection A volume p 1 →ₗ[ℝ] ∀ x, V x where
  toFun := toSection hp
  map_add' := toSection_add hp
  map_smul' := toSection_smul hp

@[simp]
theorem toSectionₗ_apply (hp : 2 < p) (w : SobolevSection A volume p 1) :
    toSectionₗ hp w = toSection hp w :=
  (rfl)

/-- The continuous representative of `0` is the zero section. -/
@[simp]
theorem toSection_zero (hp : 2 < p) : toSection hp (0 : SobolevSection A volume p 1) = 0 :=
  map_zero (toSectionₗ hp)

/-- Taking continuous representatives commutes with negation. -/
@[simp]
theorem toSection_neg (hp : 2 < p) (w : SobolevSection A volume p 1) :
    toSection hp (-w) = -toSection hp w :=
  map_neg (toSectionₗ hp) w

/-- Taking continuous representatives commutes with subtraction. -/
@[simp]
theorem toSection_sub (hp : 2 < p) (w v : SobolevSection A volume p 1) :
    toSection hp (w - v) = toSection hp w - toSection hp v :=
  map_sub (toSectionₗ hp) w v

/-- The chart expressions of the continuous representative are, on the chart images, the precise
representatives of the chart expressions of any section whose coordinates are the chart data. -/
theorem eqOn_coord_toSection (hp : 2 < p) {w : SobolevSection A volume p 1} {s : ∀ x, V x}
    (hs : ∀ i, A.sectionChartData.chartValueL volume p 1 i w
      =ᵐ[volume.restrict (A.image i)] A.coord i s)
    (i : Fin A.n) :
    EqOn (A.coord i (toSection hp w)) (preciseRepresentative volume (A.coord i s))
      (A.image i) := by
  have hu := memWkpLoc_coord w hs i
  refine (eqOn_preciseRepresentative_of_continuousOn (A.image i).isOpen
    (hu.memLpLoc.locallyIntegrableOn Fact.out (A.image i).isOpen.isLocallyClosed) ?_
    (A.continuousOn_coord (continuous_toSection hp w) i)).symm
  exact (hs i).symm.trans (chartValueL_ae_eq_coord_toSection hp w i)

/-- **Morrey's embedding for Sobolev sections: Hölder continuity in charts.** For `2 < p ≤ ∞`,
the chart expression of the continuous representative of an element of `W^{1,p}(V)` is Hölder
continuous with exponent `1 - 2 / p` on every compact subset of the chart image. -/
theorem exists_holderOnWith_coord_toSection (hp : 2 < p) (w : SobolevSection A volume p 1)
    (i : Fin A.n) {K : Set ℂ} (hK : IsCompact K) (hKi : K ⊆ A.image i) :
    ∃ C : ℝ≥0, HolderOnWith C ((1 : ℝ≥0∞) - 2 / p).toNNReal (A.coord i (toSection hp w)) K := by
  obtain ⟨s, hs⟩ := A.sectionChartData.exists_section volume p 1 w
  replace hs (i : Fin A.n) := (hs i).trans (A.sectionChartData_coord_ae_eq volume i s)
  obtain ⟨C, hC⟩ :=
    (memWkpLoc_coord w hs i).exists_holderOnWith_preciseRepresentative_of_isCompact hp hK hKi
  refine ⟨C, fun x hx y hy ↦ ?_⟩
  rw [eqOn_coord_toSection hp hs i (hKi hx), eqOn_coord_toSection hp hs i (hKi hy)]
  exact hC x hx y hy

end SobolevSection

end TauCeti
