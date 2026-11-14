/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.SobolevEmbedding
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Exponent
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Morrey

/-!
# Morrey's embedding for Sobolev sections of higher order

Let `M` be a manifold without boundary modelled on `ℂ`, let `V → M` be a real vector bundle with
finite-dimensional model fibre `F`, let `A` be a finite bundle atlas, and let `k : ℕ` and
`1 ≤ p ≤ ∞` with `2 < k p`. This file proves that every element `w` of the Sobolev space
`W^{k,p}(V)` of `TauCeti.SobolevSection A volume p k` has a unique continuous representative:
there is exactly one continuous section `s` of `V` whose coordinates in every chart `i` of `A`
agree almost everywhere on `A.image i` with the chart data of `w`
(`TauCeti.SobolevSection.existsUnique_continuous_ae_eq_coord_of_two_lt_mul`). It is
`TauCeti.SobolevSection.toSectionOfTwoLtMul`. For `k = 1` this is `p > 2`, the case of
`TauCeti.SobolevSection.toSection` (`TauCeti.SobolevSection.toSectionOfTwoLtMul_eq_toSection`);
for `k ≥ 2` it covers exponents `p ≤ 2`, where `W^{1,p}` functions need not be continuous.

The proof is that of `TauCeti.SobolevSection.existsUnique_continuous_ae_eq_coord`, with the
planar Morrey embedding for `kp > 2`
(`TauCeti.MemWkpLoc.continuousOn_preciseRepresentative_of_two_lt_mul`) in place of the one for
`W^{1,p}`, `p > 2`: the precise representatives of the chart expressions are continuous on the
chart images, satisfy the cocycle relation of the bundle on the overlaps, and glue to a continuous
section. The chart expressions of the representative are bounded on compact subsets of the chart
images by a multiple of the Sobolev norm
(`TauCeti.SobolevSection.exists_norm_coord_toSectionOfTwoLtMul_le`), by the closed graph theorem
for the map to continuous functions on a compact set.

## Main results

* `TauCeti.SobolevSection.existsUnique_continuous_ae_eq_coord_of_two_lt_mul`: an element of
  `W^{k,p}(V)`, for `2 < k p`, has a unique continuous representative.
* `TauCeti.SobolevSection.toSectionOfTwoLtMul`: that continuous section; it is linear, and
  `TauCeti.SobolevSection.toSectionOfTwoLtMulₗ` packages it as a real-linear map.
* `TauCeti.SobolevSection.toSectionOfTwoLtMul_injective`: distinct elements have distinct
  continuous representatives.
* `TauCeti.SobolevSection.toSectionOfTwoLtMul_lowerOrderL`,
  `TauCeti.SobolevSection.toSectionOfTwoLtMul_ofExponentLEL`: the continuous representative does
  not change when the order or the exponent is lowered, as long as `2 < k p` still holds.
* `TauCeti.SobolevSection.toSectionOfTwoLtMul_ofContMDiffSection`: a `Cᵏ` section is its own
  continuous representative.
* `TauCeti.SobolevSection.exists_norm_coord_toSectionOfTwoLtMul_le`: the sup bound of the chart
  expressions on compact subsets of the chart images.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 (Sobolev spaces of sections and the Sobolev embedding theorem).
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
`TauCeti.SobolevSection.existsUnique_continuous_ae_eq_coord_of_two_lt_mul`: given a section `s`
whose chart expressions are in `MemWkpLoc p (A.image i) k`, for `2 < k p`, the precise
representatives of its chart expressions are the chart expressions of a continuous section on the
chart images. -/
private theorem exists_continuous_eqOn_preciseRepresentative_of_two_lt_mul
    (hkp : 2 < (k : ℝ≥0∞) * p) {s : ∀ x, V x}
    (hs : ∀ i, MemWkpLoc p (A.image i) k (A.coord i s)) :
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

/-- **Morrey's embedding for Sobolev sections of higher order: continuous representatives.** For
`1 ≤ p ≤ ∞` and `2 < k p`, every element `w` of `W^{k,p}(V)` has exactly one continuous
representative: there is a unique continuous section `s` of `V` whose chart expression
`A.coord i s` agrees, for every chart `i`, almost everywhere on `A.image i` with the chart data of
`w`. -/
theorem existsUnique_continuous_ae_eq_coord_of_two_lt_mul (hkp : 2 < (k : ℝ≥0∞) * p)
    (w : SobolevSection A volume p k) :
    ∃! s : ∀ x, V x, Continuous (fun x ↦ TotalSpace.mk' F x (s x)) ∧
      ∀ i, A.sectionChartData.chartValueL volume p k i w
        =ᵐ[volume.restrict (A.image i)] A.coord i s := by
  obtain ⟨s, hs⟩ := A.sectionChartData.exists_section volume p k w
  replace hs (i : Fin A.n) := (hs i).trans (A.sectionChartData_coord_ae_eq volume i s)
  obtain ⟨t, ht, hts⟩ :=
    exists_continuous_eqOn_preciseRepresentative_of_two_lt_mul hkp fun i ↦ memWkpLoc_coord w hs i
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
(`TauCeti.SobolevSection.existsUnique_continuous_ae_eq_coord_of_two_lt_mul`). -/
def toSectionOfTwoLtMul (hkp : 2 < (k : ℝ≥0∞) * p) (w : SobolevSection A volume p k) :
    ∀ x, V x :=
  (existsUnique_continuous_ae_eq_coord_of_two_lt_mul hkp w).exists.choose

/-- The continuous representative is a continuous section. -/
theorem continuous_toSectionOfTwoLtMul (hkp : 2 < (k : ℝ≥0∞) * p)
    (w : SobolevSection A volume p k) :
    Continuous fun x ↦ TotalSpace.mk' F x (toSectionOfTwoLtMul hkp w x) :=
  (existsUnique_continuous_ae_eq_coord_of_two_lt_mul hkp w).exists.choose_spec.1

/-- The chart data of an element of `W^{k,p}(V)` are the chart expressions of its continuous
representative, almost everywhere. -/
theorem chartValueL_ae_eq_coord_toSectionOfTwoLtMul (hkp : 2 < (k : ℝ≥0∞) * p)
    (w : SobolevSection A volume p k) (i : Fin A.n) :
    A.sectionChartData.chartValueL volume p k i w
      =ᵐ[volume.restrict (A.image i)] A.coord i (toSectionOfTwoLtMul hkp w) :=
  (existsUnique_continuous_ae_eq_coord_of_two_lt_mul hkp w).exists.choose_spec.2 i

/-- **Uniqueness of the continuous representative.** A continuous section whose chart
expressions agree almost everywhere with the chart data of `w` is the continuous representative
of `w`. -/
theorem eq_toSectionOfTwoLtMul (hkp : 2 < (k : ℝ≥0∞) * p) {w : SobolevSection A volume p k}
    {s : ∀ x, V x} (hs : Continuous fun x ↦ TotalSpace.mk' F x (s x))
    (hw : ∀ i, A.sectionChartData.chartValueL volume p k i w
      =ᵐ[volume.restrict (A.image i)] A.coord i s) :
    s = toSectionOfTwoLtMul hkp w :=
  (existsUnique_continuous_ae_eq_coord_of_two_lt_mul hkp w).unique ⟨hs, hw⟩
    ⟨continuous_toSectionOfTwoLtMul hkp w, chartValueL_ae_eq_coord_toSectionOfTwoLtMul hkp w⟩

/-- **Injectivity.** Distinct elements of `W^{k,p}(V)` have distinct continuous
representatives. -/
theorem toSectionOfTwoLtMul_injective (hkp : 2 < (k : ℝ≥0∞) * p) :
    Function.Injective (toSectionOfTwoLtMul hkp : SobolevSection A volume p k → ∀ x, V x) :=
  fun w w' h ↦ eq_of_ae_eq_coord (chartValueL_ae_eq_coord_toSectionOfTwoLtMul hkp w)
    (h ▸ chartValueL_ae_eq_coord_toSectionOfTwoLtMul hkp w')

/-- For `k = 1` the continuous representative is `TauCeti.SobolevSection.toSection`. -/
theorem toSectionOfTwoLtMul_eq_toSection (hkp : 2 < ((1 : ℕ) : ℝ≥0∞) * p) (hp : 2 < p)
    (w : SobolevSection A volume p 1) : toSectionOfTwoLtMul hkp w = toSection hp w :=
  eq_toSection hp (continuous_toSectionOfTwoLtMul hkp w)
    (chartValueL_ae_eq_coord_toSectionOfTwoLtMul hkp w)

/-- Forgetting the highest derivative does not change the continuous representative. -/
theorem toSectionOfTwoLtMul_lowerOrderL (hkp : 2 < (k : ℝ≥0∞) * p)
    (hkp' : 2 < ((k + 1 : ℕ) : ℝ≥0∞) * p) (w : SobolevSection A volume p (k + 1)) :
    toSectionOfTwoLtMul hkp (A.sectionChartData.lowerOrderL volume p k w) =
      toSectionOfTwoLtMul hkp' w :=
  (eq_toSectionOfTwoLtMul hkp (continuous_toSectionOfTwoLtMul hkp' w) fun i ↦ by
    rw [SectionChartData.chartValueL_coe_lowerOrderL]
    exact chartValueL_ae_eq_coord_toSectionOfTwoLtMul hkp' w i).symm

/-- Lowering the exponent does not change the continuous representative. -/
theorem toSectionOfTwoLtMul_ofExponentLEL {q : ℝ≥0∞} [Fact (1 ≤ q)] (hpq : p ≤ q)
    (hkp : 2 < (k : ℝ≥0∞) * p) (hkq : 2 < (k : ℝ≥0∞) * q) (w : SobolevSection A volume q k) :
    toSectionOfTwoLtMul hkp (A.sectionChartData.ofExponentLEL volume k hpq w) =
      toSectionOfTwoLtMul hkq w :=
  (eq_toSectionOfTwoLtMul hkp (continuous_toSectionOfTwoLtMul hkq w) fun i ↦ by
    rw [SectionChartData.chartValueL_ofExponentLEL, Lp.coeFn_ofExponentLEL]
    exact chartValueL_ae_eq_coord_toSectionOfTwoLtMul hkq w i).symm

/-- The continuous representative of a `Cᵏ` section, viewed as an element of `W^{k,p}(V)`, is the
section itself. -/
@[simp]
theorem toSectionOfTwoLtMul_ofContMDiffSection [IsManifold 𝓘(ℝ, ℂ) k M]
    [ContMDiffVectorBundle k F V 𝓘(ℝ, ℂ)] (hkp : 2 < (k : ℝ≥0∞) * p)
    (s : Cₛ^k⟮𝓘(ℝ, ℂ); F, V⟯) :
    toSectionOfTwoLtMul hkp (ofContMDiffSection A volume p k s) = s :=
  (eq_toSectionOfTwoLtMul hkp s.contMDiff.continuous
    (chartValueL_ofContMDiffSection_ae A volume p k s)).symm

/-- Taking continuous representatives is additive. -/
@[simp]
theorem toSectionOfTwoLtMul_add (hkp : 2 < (k : ℝ≥0∞) * p) (w v : SobolevSection A volume p k) :
    toSectionOfTwoLtMul hkp (w + v) = toSectionOfTwoLtMul hkp w + toSectionOfTwoLtMul hkp v := by
  refine (eq_toSectionOfTwoLtMul hkp ?_ fun i ↦ ?_).symm
  · exact contMDiff_zero_iff.1 (ContMDiff.add_section (I := 𝓘(ℝ, ℂ))
      (contMDiff_zero_iff.2 (continuous_toSectionOfTwoLtMul hkp w))
      (contMDiff_zero_iff.2 (continuous_toSectionOfTwoLtMul hkp v)))
  · filter_upwards [Lp.coeFn_add (A.sectionChartData.chartValueL volume p k i w)
        (A.sectionChartData.chartValueL volume p k i v),
      chartValueL_ae_eq_coord_toSectionOfTwoLtMul hkp w i,
      chartValueL_ae_eq_coord_toSectionOfTwoLtMul hkp v i,
      ae_restrict_mem (A.image i).isOpen.measurableSet] with y hy hw hv hyU
    rw [AddMemClass.coe_add, map_add, hy, Pi.add_apply, hw, hv, A.coord_add i _ _ hyU]

/-- Taking continuous representatives commutes with real scalar multiplication. -/
@[simp]
theorem toSectionOfTwoLtMul_smul (hkp : 2 < (k : ℝ≥0∞) * p) (c : ℝ)
    (w : SobolevSection A volume p k) :
    toSectionOfTwoLtMul hkp (c • w) = c • toSectionOfTwoLtMul hkp w := by
  refine (eq_toSectionOfTwoLtMul hkp ?_ fun i ↦ ?_).symm
  · exact contMDiff_zero_iff.1 (ContMDiff.const_smul_section (I := 𝓘(ℝ, ℂ)) (a := c)
      (contMDiff_zero_iff.2 (continuous_toSectionOfTwoLtMul hkp w)))
  · filter_upwards [Lp.coeFn_smul c (A.sectionChartData.chartValueL volume p k i w),
      chartValueL_ae_eq_coord_toSectionOfTwoLtMul hkp w i,
      ae_restrict_mem (A.image i).isOpen.measurableSet] with y hy hw hyU
    rw [SetLike.val_smul, map_smul, hy, Pi.smul_apply, hw, A.coord_smul i _ _ hyU]

/-- Taking continuous representatives, as a real-linear map from `W^{k,p}(V)` to sections. -/
def toSectionOfTwoLtMulₗ (hkp : 2 < (k : ℝ≥0∞) * p) :
    SobolevSection A volume p k →ₗ[ℝ] ∀ x, V x where
  toFun := toSectionOfTwoLtMul hkp
  map_add' := toSectionOfTwoLtMul_add hkp
  map_smul' := toSectionOfTwoLtMul_smul hkp

@[simp]
theorem toSectionOfTwoLtMulₗ_apply (hkp : 2 < (k : ℝ≥0∞) * p) (w : SobolevSection A volume p k) :
    toSectionOfTwoLtMulₗ hkp w = toSectionOfTwoLtMul hkp w :=
  (rfl)

/-- The continuous representative of `0` is the zero section. -/
@[simp]
theorem toSectionOfTwoLtMul_zero (hkp : 2 < (k : ℝ≥0∞) * p) :
    toSectionOfTwoLtMul hkp (0 : SobolevSection A volume p k) = 0 :=
  map_zero (toSectionOfTwoLtMulₗ hkp)

/-- Taking continuous representatives commutes with negation. -/
@[simp]
theorem toSectionOfTwoLtMul_neg (hkp : 2 < (k : ℝ≥0∞) * p) (w : SobolevSection A volume p k) :
    toSectionOfTwoLtMul hkp (-w) = -toSectionOfTwoLtMul hkp w :=
  map_neg (toSectionOfTwoLtMulₗ hkp) w

/-- Taking continuous representatives commutes with subtraction. -/
@[simp]
theorem toSectionOfTwoLtMul_sub (hkp : 2 < (k : ℝ≥0∞) * p) (w v : SobolevSection A volume p k) :
    toSectionOfTwoLtMul hkp (w - v) = toSectionOfTwoLtMul hkp w - toSectionOfTwoLtMul hkp v :=
  map_sub (toSectionOfTwoLtMulₗ hkp) w v

/-- The chart expression in chart `i` of the continuous representative, restricted to a compact
subset `L` of the chart image, as a linear map into the continuous functions on `L`. -/
private def coordRestrictₗ (hkp : 2 < (k : ℝ≥0∞) * p) (i : Fin A.n) {L : Set ℂ}
    (hLi : L ⊆ A.image i) : SobolevSection A volume p k →ₗ[ℝ] C(L, F) where
  toFun w := ⟨fun y ↦ A.coord i (toSectionOfTwoLtMul hkp w) y,
    ((A.continuousOn_coord (continuous_toSectionOfTwoLtMul hkp w) i).mono hLi).domRestrict⟩
  map_add' w v := by
    ext y
    change A.coord i (toSectionOfTwoLtMul hkp (w + v)) y =
      A.coord i (toSectionOfTwoLtMul hkp w) y + A.coord i (toSectionOfTwoLtMul hkp v) y
    rw [toSectionOfTwoLtMul_add, A.coord_add i _ _ (hLi y.2)]
  map_smul' c w := by
    ext y
    change A.coord i (toSectionOfTwoLtMul hkp (c • w)) y =
      c • A.coord i (toSectionOfTwoLtMul hkp w) y
    rw [toSectionOfTwoLtMul_smul, A.coord_smul i _ _ (hLi y.2)]

/-- **Morrey's embedding for Sobolev sections of higher order: the sup bound.** For `2 < k p`, the
chart expression of the continuous representative is bounded on every compact subset `K` of the
chart image by a constant multiple of the Sobolev norm. The proof is the closed graph theorem for
the map to the continuous functions on a compact neighbourhood of `K`: limits in `W^{k,p}(V)` give
limits of the chart data in `Lᵖ`, hence almost everywhere along a subsequence. -/
theorem exists_norm_coord_toSectionOfTwoLtMul_le (hkp : 2 < (k : ℝ≥0∞) * p) (i : Fin A.n)
    {K : Set ℂ} (hK : IsCompact K) (hKi : K ⊆ A.image i) :
    ∃ C, ∀ w : SobolevSection A volume p k, ∀ y ∈ K,
      ‖A.coord i (toSectionOfTwoLtMul hkp w) y‖ ≤ C * ‖w‖ := by
  obtain ⟨U, hKU, hUi, hUc⟩ := Opens.exists_between_and_isCompact_closure hK hKi
  set L := closure (U : Set ℂ)
  have : CompactSpace L := isCompact_iff_compactSpace.1 hUc
  set Φ := coordRestrictₗ (A := A) hkp i hUi
  have hΦ : Continuous Φ := by
    classical
    refine Φ.continuous_of_seq_closed_graph fun w w₀ g hw hg ↦ ?_
    -- Along a subsequence the chart data converge almost everywhere.
    have hval : Tendsto (fun n ↦ A.sectionChartData.chartValueL volume p k i (w n)) atTop
        (𝓝 (A.sectionChartData.chartValueL volume p k i w₀)) :=
      ((A.sectionChartData.chartValueL volume p k i).continuous.comp
        continuous_subtype_val).continuousAt.tendsto.comp hw
    obtain ⟨ns, hns_mono, hns⟩ := (tendstoInMeasure_of_tendsto_Lp hval).exists_seq_tendsto_ae
    have hae : ∀ᵐ y ∂volume.restrict (A.image i), Tendsto
        (fun n ↦ A.coord i (toSectionOfTwoLtMul hkp (w (ns n))) y) atTop
        (𝓝 (A.coord i (toSectionOfTwoLtMul hkp w₀) y)) := by
      filter_upwards [hns, ae_all_iff.2 fun n ↦
          chartValueL_ae_eq_coord_toSectionOfTwoLtMul hkp (w (ns n)) i,
        chartValueL_ae_eq_coord_toSectionOfTwoLtMul hkp w₀ i] with y hy hn h₀
      simpa only [hn, h₀] using hy
    -- The limit `g` agrees with the chart expression of the representative of the limit on `U`,
    -- hence on its closure.
    set g' : ℂ → F := fun y ↦ if h : y ∈ L then g ⟨y, h⟩ else 0
    have hg' : ContinuousOn g' L := by
      rw [continuousOn_iff_continuous_domRestrict]
      convert g.continuous using 1
      funext y
      simp [g', y.2]
    have heqU : EqOn g' (A.coord i (toSectionOfTwoLtMul hkp w₀)) U := by
      refine Measure.eqOn_open_of_ae_eq (μ := volume) ?_ U.isOpen (hg'.mono subset_closure)
        ((A.continuousOn_coord (continuous_toSectionOfTwoLtMul hkp w₀) i).mono
          (subset_closure.trans hUi))
      filter_upwards [ae_restrict_of_ae_restrict_of_subset (subset_closure.trans hUi) hae,
        ae_restrict_mem U.isOpen.measurableSet] with y hy hyU
      have hyL : y ∈ L := subset_closure hyU
      have hgy : Tendsto (fun n ↦ A.coord i (toSectionOfTwoLtMul hkp (w (ns n))) y) atTop
          (𝓝 (g' y)) := by
        rw [show g' y = g ⟨y, hyL⟩ from dite_eq_left_of_eq_true (eq_true hyL)]
        exact ((continuous_eval_const (⟨y, hyL⟩ : L)).tendsto g).comp
          (hg.comp hns_mono.tendsto_atTop)
      exact tendsto_nhds_unique hgy hy
    have heqL : EqOn g' (A.coord i (toSectionOfTwoLtMul hkp w₀)) L :=
      heqU.of_subset_closure hg' ((A.continuousOn_coord
        (continuous_toSectionOfTwoLtMul hkp w₀) i).mono hUi) subset_closure subset_rfl
    ext y
    have hy := heqL y.2
    rw [show g' y = g y from dite_eq_left_of_eq_true (eq_true y.2)] at hy
    exact hy
  set Ψ : SobolevSection A volume p k →L[ℝ] C(L, F) := ⟨Φ, hΦ⟩
  refine ⟨‖Ψ‖, fun w y hy ↦ ?_⟩
  have hyL : y ∈ L := subset_closure (hKU hy)
  calc ‖A.coord i (toSectionOfTwoLtMul hkp w) y‖ = ‖Ψ w ⟨y, hyL⟩‖ := rfl
    _ ≤ ‖Ψ w‖ := (Ψ w).norm_coe_le_norm _
    _ ≤ ‖Ψ‖ * ‖w‖ := Ψ.le_opNorm w

/-- **Check.** `W^{2,3/2}(V)` lies below the exponent `2` of `W^{1,p}`, but `2 · 3/2 = 3 > 2`, so
its elements have continuous representatives. -/
example [Fact (1 ≤ (3 / 2 : ℝ≥0∞))] (w : SobolevSection A volume (3 / 2) 2) :
    Continuous fun x ↦ TotalSpace.mk' F x (toSectionOfTwoLtMul (by
      rw [show ((2 : ℕ) : ℝ≥0∞) * (3 / 2) = 3 by
        rw [Nat.cast_ofNat, ENNReal.mul_div_cancel two_ne_zero ENNReal.ofNat_ne_top]]
      norm_num) w x) :=
  continuous_toSectionOfTwoLtMul _ w

end SobolevSection

end TauCeti
