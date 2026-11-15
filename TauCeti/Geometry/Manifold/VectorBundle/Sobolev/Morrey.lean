/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Morrey
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.AEEq
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.ContMDiffSection
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Exponent
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Local
import TauCeti.Analysis.Sobolev.Local.SobolevEmbedding

/-!
# Morrey's embedding for Sobolev sections over surfaces

Let `M` be a manifold without boundary modelled on `ℂ`, let `V → M` be a real vector bundle with
finite-dimensional model fibre `F`, let `A` be a finite bundle atlas, and let `k : ℕ` and
`1 ≤ p ≤ ∞` with `2 < k p`. This file proves that every element `w` of the Sobolev space
`W^{k,p}(V)` of `TauCeti.SobolevSection A volume p k` has a unique continuous representative:
there is exactly one continuous section `s` of `V` whose coordinates in every chart `i` of `A`
agree almost everywhere on `A.image i` with the chart data of `w`
(`TauCeti.SobolevSection.existsUnique_continuous_ae_eq_coord`). It is
`TauCeti.SobolevSection.toSection`. Its chart expressions are bounded on compact subsets of the
chart images by a multiple of the Sobolev norm
(`TauCeti.SobolevSection.exists_norm_coord_toSection_le`), and for `p > 2` they are Hölder
continuous with exponent `1 - 2 / p` there
(`TauCeti.SobolevSection.exists_holderOnWith_coord_toSection`). For `k = 1` the hypothesis is
`p > 2`; for `k ≥ 2` it also covers exponents `p ≤ 2`, where `W^{1,p}` functions need not be
continuous.

The proof is local. An element `w` consists of the components of some section `s`, defined only up
to null sets, whose chart expression `A.coord i s` lies in `MemWkpLoc p (A.image i) k`
(`TauCeti.SobolevSection.memWkpLoc_coord`). By the planar Morrey embedding its precise
representative `gᵢ` is continuous on `A.image i`
(`TauCeti.MemWkpLoc.continuousOn_preciseRepresentative_of_two_lt_mul`) and agrees with
`A.coord i s` almost everywhere there. The coordinates of `s` in two charts are related by the
coordinate change of the bundle at every point of the overlap; since chart transitions preserve
null sets, the representatives `gᵢ` satisfy the same relation almost everywhere, and hence
everywhere, both sides being continuous on the open overlap and Lebesgue measure charging every
nonempty open set. Therefore the representatives `gᵢ` glue to a continuous section with chart
expression `gᵢ` on `A.image i` for every chart `i`
(`TauCeti.FiniteBundleAtlas.exists_continuous_coord_eqOn`). Uniqueness holds because two
continuous sections whose chart expressions agree almost everywhere agree everywhere
(`TauCeti.FiniteBundleAtlas.eq_of_continuous_of_coord_ae_eq`). The sup bound is the closed graph
theorem for the map to continuous functions on a compact neighbourhood of the compact set.

The hypothesis `2 < k p` cannot be dropped: in dimension two the space `W^{1,2}` contains
unbounded functions.

## Main results

* `TauCeti.SobolevSection.existsUnique_continuous_ae_eq_coord`: an element of `W^{k,p}(V)`, for
  `2 < k p`, has a unique continuous representative.
* `TauCeti.SobolevSection.toSection`: that continuous section; it is linear in the element of
  `W^{k,p}(V)`, and `TauCeti.SobolevSection.toSectionL` packages it as a continuous real-linear
  map to sections with the topology of pointwise convergence.
* `TauCeti.SobolevSection.toSection_injective`: distinct elements have distinct continuous
  representatives, and `TauCeti.SobolevSection.toSection_ofContMDiffSection`: a `Cᵏ` section is
  its own continuous representative.
* `TauCeti.SobolevSection.toSection_lowerOrderL`, `TauCeti.SobolevSection.toSection_ofExponentLEL`:
  the continuous representative does not change when the order or the exponent is lowered, as
  long as `2 < k p` still holds.
* `TauCeti.SobolevSection.exists_norm_coord_toSection_le`: the sup bound of the chart expressions
  on compact subsets of the chart images, and `TauCeti.SobolevSection.evalL`: evaluation of the
  continuous representative at a point is a continuous linear map to the fibre.
* `TauCeti.SobolevSection.exists_holderOnWith_coord_toSection`: for `p > 2`, the chart expressions
  are `(1 - 2 / p)`-Hölder on compact subsets of the chart images.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 (Sobolev spaces of sections and the Sobolev embedding theorem).
* R. S. Palais, *Foundations of Global Non-linear Analysis*, Benjamin (1968), §9.
-/

public section

noncomputable section

open Bundle Filter MeasureTheory Module Set TopologicalSpace TauCeti.MeasureTheory
open scoped Manifold ENNReal NNReal Topology

namespace TauCeti

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℝ, ℂ) 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  {A : FiniteBundleAtlas ℂ M F V} {p : ℝ≥0∞} [Fact (1 ≤ p)] {k : ℕ}

namespace SobolevSection

open FiniteBundleAtlas

/-- The representatives constructed in the proof of
`TauCeti.SobolevSection.existsUnique_continuous_ae_eq_coord`: given a section `s` whose chart
expressions are in `MemWkpLoc p (A.image i) k`, for `2 < k p`, the precise representatives of its
chart expressions are the chart expressions of a continuous section on the chart images. -/
private theorem exists_continuous_eqOn_preciseRepresentative (hkp : 2 < (k : ℝ≥0∞) * p)
    {s : ∀ x, V x} (hs : ∀ i, MemWkpLoc p (A.image i) k (A.coord i s)) :
    ∃ t : ∀ x, V x, Continuous (fun x ↦ TotalSpace.mk' F x (t x)) ∧
      ∀ i, EqOn (A.coord i t) (preciseRepresentative volume (A.coord i s)) (A.image i) := by
  set g : Fin A.n → ℂ → F := fun i ↦ preciseRepresentative volume (A.coord i s)
  have hg_cont (i : Fin A.n) : ContinuousOn (g i) (A.image i) :=
    (hs i).continuousOn_preciseRepresentative_of_two_lt_mul Fact.out hkp
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

/-- **Morrey's embedding for Sobolev sections: continuous representatives.** For `1 ≤ p ≤ ∞`
and `2 < k p`, every element `w` of `W^{k,p}(V)` has exactly one continuous representative: there
is a unique continuous section `s` of `V` whose chart expression `A.coord i s` agrees, for every
chart `i`, almost everywhere on `A.image i` with the chart data of `w`. -/
theorem existsUnique_continuous_ae_eq_coord (hkp : 2 < (k : ℝ≥0∞) * p)
    (w : SobolevSection A volume p k) :
    ∃! s : ∀ x, V x, Continuous (fun x ↦ TotalSpace.mk' F x (s x)) ∧
      ∀ i, A.sectionChartData.chartValueL volume p k i w
        =ᵐ[volume.restrict (A.image i)] A.coord i s := by
  obtain ⟨s, hs⟩ := A.sectionChartData.exists_section volume p k w
  replace hs (i : Fin A.n) := (hs i).trans (A.sectionChartData_coord_ae_eq volume i s)
  obtain ⟨t, ht, hts⟩ :=
    exists_continuous_eqOn_preciseRepresentative hkp fun i ↦ memWkpLoc_coord w hs i
  have hae (i : Fin A.n) :
      A.sectionChartData.chartValueL volume p k i w
        =ᵐ[volume.restrict (A.image i)] A.coord i t := by
    filter_upwards [hs i, (memWkpLoc_coord w hs i).memLpLoc.ae_eq_preciseRepresentative Fact.out,
      ae_restrict_mem (A.image i).isOpen.measurableSet] with y hy hy' hyU
    rw [hy, hy', hts i hyU]
  exact ⟨t, ⟨ht, hae⟩, fun t' ht' ↦ A.eq_of_continuous_of_coord_ae_eq (μ := volume) ht'.1 ht
    fun i ↦ (ht'.2 i).symm.trans (hae i)⟩

/-- The continuous representative of an element of `W^{k,p}(V)`, for `2 < k p`: the unique
continuous section whose chart expressions agree almost everywhere with the chart data
(`TauCeti.SobolevSection.existsUnique_continuous_ae_eq_coord`). -/
def toSection (hkp : 2 < (k : ℝ≥0∞) * p) (w : SobolevSection A volume p k) : ∀ x, V x :=
  (existsUnique_continuous_ae_eq_coord hkp w).exists.choose

/-- The continuous representative is a continuous section. -/
theorem continuous_toSection (hkp : 2 < (k : ℝ≥0∞) * p) (w : SobolevSection A volume p k) :
    Continuous fun x ↦ TotalSpace.mk' F x (toSection hkp w x) :=
  (existsUnique_continuous_ae_eq_coord hkp w).exists.choose_spec.1

/-- The chart data of an element of `W^{k,p}(V)` are the chart expressions of its continuous
representative, almost everywhere. -/
theorem chartValueL_ae_eq_coord_toSection (hkp : 2 < (k : ℝ≥0∞) * p)
    (w : SobolevSection A volume p k) (i : Fin A.n) :
    A.sectionChartData.chartValueL volume p k i w
      =ᵐ[volume.restrict (A.image i)] A.coord i (toSection hkp w) :=
  (existsUnique_continuous_ae_eq_coord hkp w).exists.choose_spec.2 i

/-- **Uniqueness of the continuous representative.** A continuous section whose chart
expressions agree almost everywhere with the chart data of `w` is the continuous representative
of `w`. -/
theorem eq_toSection (hkp : 2 < (k : ℝ≥0∞) * p) {w : SobolevSection A volume p k}
    {s : ∀ x, V x} (hs : Continuous fun x ↦ TotalSpace.mk' F x (s x))
    (hw : ∀ i, A.sectionChartData.chartValueL volume p k i w
      =ᵐ[volume.restrict (A.image i)] A.coord i s) :
    s = toSection hkp w :=
  (existsUnique_continuous_ae_eq_coord hkp w).unique ⟨hs, hw⟩
    ⟨continuous_toSection hkp w, chartValueL_ae_eq_coord_toSection hkp w⟩

/-- **Injectivity.** Distinct elements of `W^{k,p}(V)` have distinct continuous
representatives. -/
theorem toSection_injective (hkp : 2 < (k : ℝ≥0∞) * p) :
    Function.Injective (toSection hkp : SobolevSection A volume p k → ∀ x, V x) :=
  fun w w' h ↦ eq_of_ae_eq_coord (chartValueL_ae_eq_coord_toSection hkp w)
    (h ▸ chartValueL_ae_eq_coord_toSection hkp w')

/-- Forgetting the highest derivative does not change the continuous representative. -/
@[simp]
theorem toSection_lowerOrderL (hkp : 2 < (k : ℝ≥0∞) * p) (w : SobolevSection A volume p (k + 1)) :
    toSection hkp (A.sectionChartData.lowerOrderL volume p k w) =
      toSection (hkp.trans_le (by gcongr; exact_mod_cast k.le_succ)) w :=
  (eq_toSection hkp (continuous_toSection _ w) fun i ↦ by
    rw [SectionChartData.chartValueL_coe_lowerOrderL]
    exact chartValueL_ae_eq_coord_toSection _ w i).symm

/-- Lowering the exponent does not change the continuous representative. -/
@[simp]
theorem toSection_ofExponentLEL {q : ℝ≥0∞} [Fact (1 ≤ q)] (hpq : p ≤ q)
    (hkp : 2 < (k : ℝ≥0∞) * p) (w : SobolevSection A volume q k) :
    toSection hkp (A.sectionChartData.ofExponentLEL volume k hpq w) =
      toSection (hkp.trans_le (by gcongr)) w :=
  (eq_toSection hkp (continuous_toSection _ w) fun i ↦ by
    rw [SectionChartData.chartValueL_ofExponentLEL, Lp.coeFn_ofExponentLEL]
    exact chartValueL_ae_eq_coord_toSection _ w i).symm

/-- The continuous representative of a `Cᵏ` section, viewed as an element of `W^{k,p}(V)`, is the
section itself. -/
@[simp]
theorem toSection_ofContMDiffSection [IsManifold 𝓘(ℝ, ℂ) k M]
    [ContMDiffVectorBundle k F V 𝓘(ℝ, ℂ)] (hkp : 2 < (k : ℝ≥0∞) * p)
    (s : Cₛ^k⟮𝓘(ℝ, ℂ); F, V⟯) :
    toSection hkp (ofContMDiffSection A volume p k s) = s :=
  (eq_toSection hkp s.contMDiff.continuous
    (chartValueL_ofContMDiffSection_ae A volume p k s)).symm

/-- Taking continuous representatives is additive. -/
@[simp]
theorem toSection_add (hkp : 2 < (k : ℝ≥0∞) * p) (w v : SobolevSection A volume p k) :
    toSection hkp (w + v) = toSection hkp w + toSection hkp v := by
  refine (eq_toSection hkp ?_ fun i ↦ ?_).symm
  · exact contMDiff_zero_iff.1 (ContMDiff.add_section (I := 𝓘(ℝ, ℂ))
      (contMDiff_zero_iff.2 (continuous_toSection hkp w))
      (contMDiff_zero_iff.2 (continuous_toSection hkp v)))
  · filter_upwards [Lp.coeFn_add (A.sectionChartData.chartValueL volume p k i w)
        (A.sectionChartData.chartValueL volume p k i v),
      chartValueL_ae_eq_coord_toSection hkp w i, chartValueL_ae_eq_coord_toSection hkp v i,
      ae_restrict_mem (A.image i).isOpen.measurableSet] with y hy hw hv hyU
    rw [AddMemClass.coe_add, map_add, hy, Pi.add_apply, hw, hv, A.coord_add i _ _ hyU]

/-- Taking continuous representatives commutes with real scalar multiplication. -/
@[simp]
theorem toSection_smul (hkp : 2 < (k : ℝ≥0∞) * p) (c : ℝ) (w : SobolevSection A volume p k) :
    toSection hkp (c • w) = c • toSection hkp w := by
  refine (eq_toSection hkp ?_ fun i ↦ ?_).symm
  · exact contMDiff_zero_iff.1 (ContMDiff.const_smul_section (I := 𝓘(ℝ, ℂ)) (a := c)
      (contMDiff_zero_iff.2 (continuous_toSection hkp w)))
  · filter_upwards [Lp.coeFn_smul c (A.sectionChartData.chartValueL volume p k i w),
      chartValueL_ae_eq_coord_toSection hkp w i,
      ae_restrict_mem (A.image i).isOpen.measurableSet] with y hy hw hyU
    rw [SetLike.val_smul, map_smul, hy, Pi.smul_apply, hw, A.coord_smul i _ _ hyU]

/-- The chart expressions of the continuous representative are, on the chart images, the precise
representatives of the chart expressions of any section whose coordinates are the chart data. -/
theorem eqOn_coord_toSection (hkp : 2 < (k : ℝ≥0∞) * p) {w : SobolevSection A volume p k}
    {s : ∀ x, V x}
    (hs : ∀ i, A.sectionChartData.chartValueL volume p k i w
      =ᵐ[volume.restrict (A.image i)] A.coord i s)
    (i : Fin A.n) :
    EqOn (A.coord i (toSection hkp w)) (preciseRepresentative volume (A.coord i s))
      (A.image i) := by
  have hu := memWkpLoc_coord w hs i
  refine (eqOn_preciseRepresentative_of_continuousOn (A.image i).isOpen
    (hu.memLpLoc.locallyIntegrableOn Fact.out (A.image i).isOpen.isLocallyClosed) ?_
    (A.continuousOn_coord (continuous_toSection hkp w) i)).symm
  exact (hs i).symm.trans (chartValueL_ae_eq_coord_toSection hkp w i)

/-- **Morrey's embedding for Sobolev sections: Hölder continuity in charts.** For `2 < p ≤ ∞`
and `2 < k p`, the chart expression of the continuous representative of an element of
`W^{k,p}(V)` is Hölder continuous with exponent `1 - 2 / p` on every compact subset of the chart
image. -/
theorem exists_holderOnWith_coord_toSection (hkp : 2 < (k : ℝ≥0∞) * p) (hp : 2 < p)
    (w : SobolevSection A volume p k) (i : Fin A.n) {K : Set ℂ} (hK : IsCompact K)
    (hKi : K ⊆ A.image i) :
    ∃ C : ℝ≥0, HolderOnWith C ((1 : ℝ≥0∞) - 2 / p).toNNReal (A.coord i (toSection hkp w)) K := by
  have hk : 1 ≤ k := Nat.one_le_iff_ne_zero.2 fun hk ↦ by simp [hk] at hkp
  obtain ⟨s, hs⟩ := A.sectionChartData.exists_section volume p k w
  replace hs (i : Fin A.n) := (hs i).trans (A.sectionChartData_coord_ae_eq volume i s)
  obtain ⟨C, hC⟩ := ((memWkpLoc_coord w hs i).of_le
    hk).exists_holderOnWith_preciseRepresentative_of_isCompact hp hK hKi
  refine ⟨C, fun x hx y hy ↦ ?_⟩
  rw [eqOn_coord_toSection hkp hs i (hKi hx), eqOn_coord_toSection hkp hs i (hKi hy)]
  exact hC x hx y hy

/-- The chart expression in chart `i` of the continuous representative, restricted to a subset
`L` of the chart image, as a linear map into the continuous functions on `L`. -/
private def coordRestrictₗ (hkp : 2 < (k : ℝ≥0∞) * p) (i : Fin A.n) {L : Set ℂ}
    (hLi : L ⊆ A.image i) : SobolevSection A volume p k →ₗ[ℝ] C(L, F) where
  toFun w := ⟨fun y ↦ A.coord i (toSection hkp w) y,
    ((A.continuousOn_coord (continuous_toSection hkp w) i).mono hLi).domRestrict⟩
  map_add' w v := by
    ext y
    simp only [toSection_add, ContinuousMap.add_apply, ContinuousMap.coe_mk]
    exact A.coord_add i _ _ (hLi y.2)
  map_smul' c w := by
    ext y
    simp only [toSection_smul, ContinuousMap.smul_apply, ContinuousMap.coe_mk]
    exact A.coord_smul i _ _ (hLi y.2)

private theorem coordRestrictₗ_apply (hkp : 2 < (k : ℝ≥0∞) * p) (i : Fin A.n) {L : Set ℂ}
    (hLi : L ⊆ A.image i) (w : SobolevSection A volume p k) (y : L) :
    coordRestrictₗ hkp i hLi w y = A.coord i (toSection hkp w) y :=
  rfl

/-- On the closure of an open set with compact closure inside the chart image, the chart
expression of the continuous representative depends continuously on the element of
`W^{k,p}(V)`, by the closed graph theorem: limits in `W^{k,p}(V)` give limits of the chart data in
`Lᵖ`, hence almost everywhere along a subsequence. -/
private theorem continuous_coordRestrictₗ (hkp : 2 < (k : ℝ≥0∞) * p) (i : Fin A.n)
    {U : Opens ℂ} (hUi : closure (U : Set ℂ) ⊆ A.image i) (hUc : IsCompact (closure (U : Set ℂ))) :
    Continuous (coordRestrictₗ hkp i hUi) := by
  classical
  set L := closure (U : Set ℂ)
  have : CompactSpace L := isCompact_iff_compactSpace.1 hUc
  refine (coordRestrictₗ hkp i hUi).continuous_of_seq_closed_graph fun w w₀ g hw hg ↦ ?_
  -- Along a subsequence the chart data converge almost everywhere.
  have hval : Tendsto (fun n ↦ A.sectionChartData.chartValueL volume p k i (w n)) atTop
      (𝓝 (A.sectionChartData.chartValueL volume p k i w₀)) :=
    ((A.sectionChartData.chartValueL volume p k i).continuous.comp
      continuous_subtype_val).continuousAt.tendsto.comp hw
  obtain ⟨ns, hns_mono, hns⟩ := (tendstoInMeasure_of_tendsto_Lp hval).exists_seq_tendsto_ae
  have hae : ∀ᵐ y ∂volume.restrict (A.image i), Tendsto
      (fun n ↦ A.coord i (toSection hkp (w (ns n))) y) atTop
      (𝓝 (A.coord i (toSection hkp w₀) y)) := by
    filter_upwards [hns, ae_all_iff.2 fun n ↦ chartValueL_ae_eq_coord_toSection hkp (w (ns n)) i,
      chartValueL_ae_eq_coord_toSection hkp w₀ i] with y hy hn h₀
    simpa only [hn, h₀] using hy
  -- The limit `g` agrees with the chart expression of the representative of the limit on `U`,
  -- hence on its closure.
  set g' : ℂ → F := fun y ↦ if h : y ∈ L then g ⟨y, h⟩ else 0
  have hg' : ContinuousOn g' L := by
    rw [continuousOn_iff_continuous_domRestrict]
    convert g.continuous using 1
    funext y
    simp [g', y.2]
  have hcont := A.continuousOn_coord (continuous_toSection hkp w₀) i
  have heqU : EqOn g' (A.coord i (toSection hkp w₀)) U := by
    refine Measure.eqOn_open_of_ae_eq (μ := volume) ?_ U.isOpen (hg'.mono subset_closure)
      (hcont.mono (subset_closure.trans hUi))
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (subset_closure.trans hUi) hae,
      ae_restrict_mem U.isOpen.measurableSet] with y hy hyU
    have hyL : y ∈ L := subset_closure hyU
    have hgy : Tendsto (fun n ↦ A.coord i (toSection hkp (w (ns n))) y) atTop (𝓝 (g' y)) := by
      simpa only [g', hyL, ↓reduceDIte, Function.comp_def, coordRestrictₗ_apply] using
        ((continuous_eval_const (⟨y, hyL⟩ : L)).tendsto g).comp (hg.comp hns_mono.tendsto_atTop)
    exact tendsto_nhds_unique hgy hy
  have heqL : EqOn g' (A.coord i (toSection hkp w₀)) L :=
    heqU.of_subset_closure hg' (hcont.mono hUi) subset_closure subset_rfl
  ext y
  simpa only [g', y.2, ↓reduceDIte, coordRestrictₗ_apply] using heqL y.2

/-- **Morrey's embedding for Sobolev sections: the sup bound.** For `2 < k p`, the chart
expression of the continuous representative is bounded on every compact subset `K` of the chart
image by a constant multiple of the Sobolev norm. -/
theorem exists_norm_coord_toSection_le (hkp : 2 < (k : ℝ≥0∞) * p) (i : Fin A.n)
    {K : Set ℂ} (hK : IsCompact K) (hKi : K ⊆ A.image i) :
    ∃ C : ℝ≥0, ∀ w : SobolevSection A volume p k, ∀ y ∈ K,
      ‖A.coord i (toSection hkp w) y‖ ≤ C * ‖w‖ := by
  obtain ⟨U, hKU, hUi, hUc⟩ := Opens.exists_between_and_isCompact_closure hK hKi
  have : CompactSpace (closure (U : Set ℂ)) := isCompact_iff_compactSpace.1 hUc
  let Ψ : SobolevSection A volume p k →L[ℝ] C(closure (U : Set ℂ), F) :=
    ⟨coordRestrictₗ hkp i hUi, continuous_coordRestrictₗ hkp i hUi hUc⟩
  refine ⟨‖Ψ‖₊, fun w y hy ↦ ?_⟩
  have hyL : y ∈ closure (U : Set ℂ) := subset_closure (hKU hy)
  calc ‖A.coord i (toSection hkp w) y‖ = ‖Ψ w ⟨y, hyL⟩‖ := by
        rw [ContinuousLinearMap.coe_mk', coordRestrictₗ_apply]
    _ ≤ ‖Ψ w‖ := (Ψ w).norm_coe_le_norm _
    _ ≤ ‖Ψ‖ * ‖w‖ := Ψ.le_opNorm w

/-- **Morrey's embedding for Sobolev sections: point evaluation.** For `2 < k p`, evaluating the
continuous representative at a point `x` is a continuous real-linear map from `W^{k,p}(V)` to the
fibre `V x`. -/
def evalL (hkp : 2 < (k : ℝ≥0∞) * p) (x : M) : SobolevSection A volume p k →L[ℝ] V x where
  toFun w := toSection hkp w x
  map_add' w v := by simp
  map_smul' c w := by simp
  cont := by
    obtain ⟨i, hx⟩ := A.exists_mem_dom x
    have hxi : A.chart i x ∈ A.image i := A.mem_image.2 ⟨x, hx, rfl⟩
    obtain ⟨C, hC⟩ := exists_norm_coord_toSection_le hkp i isCompact_singleton
      (singleton_subset_iff.2 hxi)
    -- The chart expression at `A.chart i x`, which determines the value at `x`.
    let φ : SobolevSection A volume p k →ₗ[ℝ] F :=
      { toFun w := A.coord i (toSection hkp w) (A.chart i x)
        map_add' w v := by simp [A.coord_add i _ _ hxi]
        map_smul' c w := by simp [A.coord_smul i _ _ hxi] }
    refine (((A.triv i).symmL ℝ x).continuous.comp
      (φ.mkContinuous C fun w ↦ hC w _ rfl).continuous).congr fun w ↦ ?_
    simp [φ, (A.triv i).symmL_apply (A.dom_subset_baseSet i hx), A.coord_chart _ hx,
      (A.triv i).symm_apply_apply_mk (A.dom_subset_baseSet i hx)]

@[simp]
theorem evalL_apply (hkp : 2 < (k : ℝ≥0∞) * p) (x : M) (w : SobolevSection A volume p k) :
    evalL hkp x w = toSection hkp w x :=
  (rfl)

/-- Taking continuous representatives, as a continuous real-linear map from `W^{k,p}(V)` to
sections, with the topology of pointwise convergence. -/
def toSectionL (hkp : 2 < (k : ℝ≥0∞) * p) : SobolevSection A volume p k →L[ℝ] ∀ x, V x :=
  ContinuousLinearMap.pi (evalL hkp)

@[simp]
theorem toSectionL_apply (hkp : 2 < (k : ℝ≥0∞) * p) (w : SobolevSection A volume p k) :
    toSectionL hkp w = toSection hkp w :=
  (rfl)

/-- The continuous representative of `0` is the zero section. -/
@[simp]
theorem toSection_zero (hkp : 2 < (k : ℝ≥0∞) * p) :
    toSection hkp (0 : SobolevSection A volume p k) = 0 :=
  map_zero (toSectionL hkp)

/-- Taking continuous representatives commutes with negation. -/
@[simp]
theorem toSection_neg (hkp : 2 < (k : ℝ≥0∞) * p) (w : SobolevSection A volume p k) :
    toSection hkp (-w) = -toSection hkp w :=
  map_neg (toSectionL hkp) w

/-- Taking continuous representatives commutes with subtraction. -/
@[simp]
theorem toSection_sub (hkp : 2 < (k : ℝ≥0∞) * p) (w v : SobolevSection A volume p k) :
    toSection hkp (w - v) = toSection hkp w - toSection hkp v :=
  map_sub (toSectionL hkp) w v

/-- **Check.** `W^{2,3/2}(V)` lies below the exponent `2` of `W^{1,p}`, but `2 · 3/2 = 3 > 2`, so
its elements have continuous representatives. -/
example [Fact (1 ≤ (3 / 2 : ℝ≥0∞))] (w : SobolevSection A volume (3 / 2) 2) :
    Continuous fun x ↦ TotalSpace.mk' F x (toSection (by
      rw [Nat.cast_ofNat, ENNReal.mul_div_cancel two_ne_zero ENNReal.ofNat_ne_top]
      norm_num) w x) :=
  continuous_toSection _ w

end SobolevSection

end TauCeti
