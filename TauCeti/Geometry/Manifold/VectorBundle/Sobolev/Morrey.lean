/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.Inclusion
public import TauCeti.Analysis.Sobolev.W1p.InteriorMorrey
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.AEEq
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.ContMDiffSection
import TauCeti.Analysis.Sobolev.W1p.PreciseRepresentative
import TauCeti.Topology.MetricSpace.Holder

/-!
# Morrey's embedding for Sobolev sections

Let `M` be a `C¹` manifold without boundary modelled on a finite-dimensional real inner product
space `E` of dimension `n`, let `V → M` be a real vector bundle with finite-dimensional model fibre
`F`, let `A` be a finite bundle atlas, let `μ` be an additive Haar measure on `E` and let
`n < p ≤ ∞`. This file proves Morrey's embedding for the Sobolev space `W^{1,p}(V)` of
`TauCeti.SobolevSection A μ p 1`, with exponent `α = 1 - n / p`.

* Every element `w` of `W^{1,p}(V)` has a unique continuous representative: there is exactly one
  continuous section `s` of `V` whose coordinates in every chart `i` of `A` agree almost everywhere
  on `A.image i` with the chart data of `w`
  (`TauCeti.SobolevSection.existsUnique_continuous_ae_eq_coord`). It is
  `TauCeti.SobolevSection.toSection`, linear and injective in `w`.
* The embedding is bounded. On every compact subset `K` of a chart image, the chart expression of
  the continuous representative is bounded by `C ‖w‖` and `α`-Hölder with constant `C ‖w‖`, where
  `C` depends on `K` but not on `w`. Restriction to `K` is therefore a continuous linear map
  `TauCeti.SobolevSection.morreyEmbedding` from `W^{1,p}(V)` to the Banach space `C^{0,α}(K; F)`
  of `TauCeti.HolderSpace`. At `p = ∞` the exponent is `1` and the chart expressions are Lipschitz.
* The embedding is compact into every `C^{0,β}(K; F)` with `β < α`
  (`TauCeti.SobolevSection.isCompactOperator_inclusionL_comp_morreyEmbedding`), by the
  Arzelà–Ascoli compactness of the Hölder inclusion `C^{0,α} → C^{0,β}`.

The proof is local. In chart `i` the components of `w` in the basis `Module.finBasis ℝ F` are
scalar Sobolev functions `w i j ∈ W^{1,p}(A.image i)`, whose precise representatives are continuous
on `A.image i` by the interior Morrey embedding
(`TauCeti.W1p.continuousOn_preciseRepresentative`). Their combination `gᵢ` with the basis vectors
is continuous on `A.image i` and agrees with the chart data there almost everywhere. The
coordinates of a section with chart data `w` in two charts are related by the coordinate change of
the bundle at every point of the overlap; since chart transitions preserve null sets, the functions
`gᵢ` satisfy the same relation almost everywhere, and hence everywhere, both sides being continuous
on the open overlap and the Haar measure charging every nonempty open set. Therefore they glue to a
continuous section with chart expression `gᵢ` on `A.image i` for every chart `i`
(`TauCeti.FiniteBundleAtlas.exists_continuous_coord_eqOn`). Uniqueness holds because two
continuous sections whose chart expressions agree almost everywhere agree everywhere
(`TauCeti.FiniteBundleAtlas.eq_of_continuous_of_coord_ae_eq`). The bounds come from the uniform
interior bounds for the scalar components,
`TauCeti.W1p.exists_forall_norm_preciseRepresentative_le_of_isCompact` and
`TauCeti.W1p.exists_forall_holderOnWith_preciseRepresentative_of_isCompact`, since every component
of `w` has norm at most `‖w‖` (`TauCeti.SectionChartData.norm_component_le`).

For `n ≥ 2` the hypothesis `n < p` cannot be weakened to `p = n`: `W^{1,n}` contains unbounded
functions, such as `log (log (e / ‖x‖))` near the origin.

## Main results

* `TauCeti.SobolevSection.existsUnique_continuous_ae_eq_coord`: an element of `W^{1,p}(V)`, for
  `p` above the dimension, has a unique continuous representative.
* `TauCeti.SobolevSection.toSection`: that continuous section; it is linear in the element of
  `W^{1,p}(V)`, and `TauCeti.SobolevSection.toSectionₗ` packages it as a real-linear map.
* `TauCeti.SobolevSection.toSection_injective`: distinct elements have distinct continuous
  representatives, and `TauCeti.SobolevSection.toSection_ofContMDiffSection`: a `C¹` section is
  its own continuous representative.
* `TauCeti.SobolevSection.repr_coord_toSection`: in chart `i`, the components of the continuous
  representative are the precise representatives of the chart-`i` components of `w`.
* `TauCeti.SobolevSection.exists_forall_norm_coord_toSection_le`,
  `TauCeti.SobolevSection.exists_forall_holderOnWith_coord_toSection` and
  `TauCeti.SobolevSection.exists_forall_lipschitzOnWith_coord_toSection`: the chart expressions are
  bounded and `α`-Hölder, Lipschitz at `p = ∞`, on compact subsets of the chart images, with
  constants `C ‖w‖`.
* `TauCeti.SobolevSection.morreyEmbedding`: the bounded operator `W^{1,p}(V) → C^{0,α}(K; F)`.
* `TauCeti.SobolevSection.isCompactOperator_inclusionL_comp_morreyEmbedding`: it is compact into
  `C^{0,β}(K; F)` for `β < α`.

## References

* C. B. Morrey, *Multiple Integrals in the Calculus of Variations*, Theorem 3.5.2.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 7.17.
* R. S. Palais, *Foundations of Global Non-linear Analysis*, Benjamin (1968), §9.
-/

public section

noncomputable section

open Bundle MeasureTheory Module Set TopologicalSpace TauCeti.MeasureTheory
open scoped Manifold ENNReal NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  {A : FiniteBundleAtlas E M F V} {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace SobolevSection

open FiniteBundleAtlas

/-- The combination of the basis vectors of the model fibre with the precise representatives of the
chart-`i` components of an element of `W^{1,p}(V)`. -/
private def chartRep (w : SobolevSection A μ p 1) (i : Fin A.n) (y : E) : F :=
  ∑ j, preciseRepresentative μ
    (W1p.value ((w : A.sectionChartData.SobolevData μ p 1) i j)) y • finBasis ℝ F j

/-- For `p` above the dimension, `chartRep w i` is continuous on the image of chart `i`. -/
private theorem continuousOn_chartRep (hp : (finrank ℝ E : ℝ≥0∞) < p)
    (w : SobolevSection A μ p 1) (i : Fin A.n) : ContinuousOn (chartRep w i) (A.image i) :=
  continuousOn_finsetSum _ fun _ _ ↦
    (W1p.continuousOn_preciseRepresentative hp _).smul continuousOn_const

/-- The chart data of `w` agree with `chartRep w i` almost everywhere on the image of chart `i`. -/
private theorem chartValueL_ae_eq_chartRep (w : SobolevSection A μ p 1) (i : Fin A.n) :
    A.sectionChartData.chartValueL μ p 1 i w =ᵐ[μ.restrict (A.image i)] chartRep w i := by
  filter_upwards [A.sectionChartData.chartValueL_apply_ae μ p 1 i w,
    ae_all_iff.2 fun j ↦ W1p.ae_eq_preciseRepresentative
      ((w : A.sectionChartData.SobolevData μ p 1) i j)] with y hy hj
  rw [hy]
  exact Finset.sum_congr rfl fun j _ ↦ by rw [Wkp.value_one, hj j]

variable [IsManifold 𝓘(ℝ, E) 1 M]

/-- **Morrey's embedding for Sobolev sections: continuous representatives.** For `p` above the
dimension `n` of the model space, `n < p ≤ ∞`, every element `w` of `W^{1,p}(V)` has exactly one
continuous representative: there is a unique continuous section `s` of `V` whose chart expression
`A.coord i s` agrees, for every chart `i`, almost everywhere on `A.image i` with the chart data of
`w`. -/
theorem existsUnique_continuous_ae_eq_coord (hp : (finrank ℝ E : ℝ≥0∞) < p)
    (w : SobolevSection A μ p 1) :
    ∃! s : ∀ x, V x, Continuous (fun x ↦ TotalSpace.mk' F x (s x)) ∧
      ∀ i, A.sectionChartData.chartValueL μ p 1 i w
        =ᵐ[μ.restrict (A.image i)] A.coord i s := by
  obtain ⟨s, hs⟩ := A.sectionChartData.exists_section μ p 1 w
  replace hs (i : Fin A.n) := (hs i).trans (A.sectionChartData_coord_ae_eq μ i s)
  have hg_ae (i : Fin A.n) : A.coord i s =ᵐ[μ.restrict (A.image i)] chartRep w i :=
    (hs i).symm.trans (chartValueL_ae_eq_chartRep w i)
  -- The functions `chartRep w i` satisfy the cocycle relation at every point of every overlap.
  have hcompat (i i' : Fin A.n) : EqOn (chartRep w i')
      (fun y ↦ (A.triv i).coordChangeL ℝ (A.triv i') ((A.chart i').symm y)
        (chartRep w i (A.transition i i' y))) (A.overlap i i') := by
    refine Measure.eqOn_open_of_ae_eq (μ := μ) ?_ (A.isOpen_overlap i i')
      ((continuousOn_chartRep hp w i').mono (A.overlap_subset_image i i'))
      (A.continuousOn_coordChange_transition (continuousOn_chartRep hp w i))
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (A.overlap_subset_image i i')
        (hg_ae i'), A.sectionChartData.aeTransition_iff.1 (A.aeTransition_sectionChartData μ)
          (i' := i') (hg_ae i),
        ae_restrict_mem (A.isOpen_overlap i i').measurableSet] with y h' h hy
    rw [A.sectionChartData_transition_of_mem hy] at h
    rw [← h', ← h, A.coord_eq_coordChange s hy]
  obtain ⟨t, ht, hts⟩ := A.exists_continuous_coord_eqOn (continuousOn_chartRep hp w) hcompat
  have hae (i : Fin A.n) :
      A.sectionChartData.chartValueL μ p 1 i w =ᵐ[μ.restrict (A.image i)] A.coord i t := by
    filter_upwards [chartValueL_ae_eq_chartRep w i,
      ae_restrict_mem (A.image i).isOpen.measurableSet] with y hy hyU
    rw [hy, hts i hyU]
  exact ⟨t, ⟨ht, hae⟩, fun t' ht' ↦ A.eq_of_continuous_of_coord_ae_eq (μ := μ) ht'.1 ht
    fun i ↦ (ht'.2 i).symm.trans (hae i)⟩

/-- The continuous representative of an element of `W^{1,p}(V)`, for `p` above the dimension: the
unique continuous section whose chart expressions agree almost everywhere with the chart data
(`TauCeti.SobolevSection.existsUnique_continuous_ae_eq_coord`). -/
def toSection (hp : (finrank ℝ E : ℝ≥0∞) < p) (w : SobolevSection A μ p 1) : ∀ x, V x :=
  (existsUnique_continuous_ae_eq_coord hp w).exists.choose

/-- The continuous representative is a continuous section. -/
theorem continuous_toSection (hp : (finrank ℝ E : ℝ≥0∞) < p) (w : SobolevSection A μ p 1) :
    Continuous fun x ↦ TotalSpace.mk' F x (toSection hp w x) :=
  (existsUnique_continuous_ae_eq_coord hp w).exists.choose_spec.1

/-- The chart data of an element of `W^{1,p}(V)` are the chart expressions of its continuous
representative, almost everywhere. -/
theorem chartValueL_ae_eq_coord_toSection (hp : (finrank ℝ E : ℝ≥0∞) < p)
    (w : SobolevSection A μ p 1) (i : Fin A.n) :
    A.sectionChartData.chartValueL μ p 1 i w
      =ᵐ[μ.restrict (A.image i)] A.coord i (toSection hp w) :=
  (existsUnique_continuous_ae_eq_coord hp w).exists.choose_spec.2 i

/-- **Uniqueness of the continuous representative.** A continuous section whose chart
expressions agree almost everywhere with the chart data of `w` is the continuous representative
of `w`. -/
theorem eq_toSection (hp : (finrank ℝ E : ℝ≥0∞) < p) {w : SobolevSection A μ p 1}
    {s : ∀ x, V x} (hs : Continuous fun x ↦ TotalSpace.mk' F x (s x))
    (hw : ∀ i, A.sectionChartData.chartValueL μ p 1 i w
      =ᵐ[μ.restrict (A.image i)] A.coord i s) :
    s = toSection hp w :=
  (existsUnique_continuous_ae_eq_coord hp w).unique ⟨hs, hw⟩
    ⟨continuous_toSection hp w, chartValueL_ae_eq_coord_toSection hp w⟩

/-- **Injectivity.** Distinct elements of `W^{1,p}(V)` have distinct continuous
representatives. -/
theorem toSection_injective (hp : (finrank ℝ E : ℝ≥0∞) < p) :
    Function.Injective (toSection hp : SobolevSection A μ p 1 → ∀ x, V x) :=
  fun w w' h ↦ eq_of_ae_eq_coord (chartValueL_ae_eq_coord_toSection hp w)
    (h ▸ chartValueL_ae_eq_coord_toSection hp w')

/-- The continuous representative of a `C¹` section, viewed as an element of `W^{1,p}(V)`, is the
section itself. The smoothness instances are stated at `(1 : ℕ)`, as in
`TauCeti.SobolevSection.ofContMDiffSection`. -/
@[simp]
theorem toSection_ofContMDiffSection [IsManifold 𝓘(ℝ, E) (1 : ℕ) M]
    [ContMDiffVectorBundle (1 : ℕ) F V 𝓘(ℝ, E)] (hp : (finrank ℝ E : ℝ≥0∞) < p)
    (s : Cₛ^(1 : ℕ)⟮𝓘(ℝ, E); F, V⟯) :
    toSection hp (ofContMDiffSection A μ p 1 s) = s :=
  (eq_toSection hp s.contMDiff.continuous
    (chartValueL_ofContMDiffSection_ae A μ p 1 s)).symm

/-- Taking continuous representatives is additive. -/
@[simp]
theorem toSection_add (hp : (finrank ℝ E : ℝ≥0∞) < p) (w v : SobolevSection A μ p 1) :
    toSection hp (w + v) = toSection hp w + toSection hp v := by
  refine (eq_toSection hp ?_ fun i ↦ ?_).symm
  · exact contMDiff_zero_iff.1 (ContMDiff.add_section (I := 𝓘(ℝ, E))
      (contMDiff_zero_iff.2 (continuous_toSection hp w))
      (contMDiff_zero_iff.2 (continuous_toSection hp v)))
  · filter_upwards [Lp.coeFn_add (A.sectionChartData.chartValueL μ p 1 i w)
        (A.sectionChartData.chartValueL μ p 1 i v),
      chartValueL_ae_eq_coord_toSection hp w i, chartValueL_ae_eq_coord_toSection hp v i,
      ae_restrict_mem (A.image i).isOpen.measurableSet] with y hy hw hv hyU
    rw [AddMemClass.coe_add, map_add, hy, Pi.add_apply, hw, hv, A.coord_add i _ _ hyU]

/-- Taking continuous representatives commutes with real scalar multiplication. -/
@[simp]
theorem toSection_smul (hp : (finrank ℝ E : ℝ≥0∞) < p) (c : ℝ) (w : SobolevSection A μ p 1) :
    toSection hp (c • w) = c • toSection hp w := by
  refine (eq_toSection hp ?_ fun i ↦ ?_).symm
  · exact contMDiff_zero_iff.1 (ContMDiff.const_smul_section (I := 𝓘(ℝ, E)) (a := c)
      (contMDiff_zero_iff.2 (continuous_toSection hp w)))
  · filter_upwards [Lp.coeFn_smul c (A.sectionChartData.chartValueL μ p 1 i w),
      chartValueL_ae_eq_coord_toSection hp w i,
      ae_restrict_mem (A.image i).isOpen.measurableSet] with y hy hw hyU
    rw [SetLike.val_smul, map_smul, hy, Pi.smul_apply, hw, A.coord_smul i _ _ hyU]

/-- Taking continuous representatives, as a real-linear map from `W^{1,p}(V)` to sections. -/
def toSectionₗ (hp : (finrank ℝ E : ℝ≥0∞) < p) : SobolevSection A μ p 1 →ₗ[ℝ] ∀ x, V x where
  toFun := toSection hp
  map_add' := toSection_add hp
  map_smul' := toSection_smul hp

@[simp]
theorem toSectionₗ_apply (hp : (finrank ℝ E : ℝ≥0∞) < p) (w : SobolevSection A μ p 1) :
    toSectionₗ hp w = toSection hp w :=
  (rfl)

/-- The continuous representative of `0` is the zero section. -/
@[simp]
theorem toSection_zero (hp : (finrank ℝ E : ℝ≥0∞) < p) :
    toSection hp (0 : SobolevSection A μ p 1) = 0 :=
  map_zero (toSectionₗ hp)

/-- Taking continuous representatives commutes with negation. -/
@[simp]
theorem toSection_neg (hp : (finrank ℝ E : ℝ≥0∞) < p) (w : SobolevSection A μ p 1) :
    toSection hp (-w) = -toSection hp w :=
  map_neg (toSectionₗ hp) w

/-- Taking continuous representatives commutes with subtraction. -/
@[simp]
theorem toSection_sub (hp : (finrank ℝ E : ℝ≥0∞) < p) (w v : SobolevSection A μ p 1) :
    toSection hp (w - v) = toSection hp w - toSection hp v :=
  map_sub (toSectionₗ hp) w v

/-- On the image of chart `i`, the chart expression of the continuous representative is
`chartRep w i`. -/
private theorem eqOn_coord_toSection_chartRep (hp : (finrank ℝ E : ℝ≥0∞) < p)
    (w : SobolevSection A μ p 1) (i : Fin A.n) :
    EqOn (A.coord i (toSection hp w)) (chartRep w i) (A.image i) :=
  Measure.eqOn_open_of_ae_eq (μ := μ)
    ((chartValueL_ae_eq_coord_toSection hp w i).symm.trans (chartValueL_ae_eq_chartRep w i))
    (A.image i).isOpen (A.continuousOn_coord (continuous_toSection hp w) i)
    (continuousOn_chartRep hp w i)

/-- **The chart components of the continuous representative.** On the image of chart `i`, the
`j`th component in the basis `Module.finBasis ℝ F` of the chart expression of the continuous
representative of `w` is the precise representative of the chart-`i` component `w i j`, a scalar
Sobolev function on the chart image. -/
theorem repr_coord_toSection (hp : (finrank ℝ E : ℝ≥0∞) < p) (w : SobolevSection A μ p 1)
    {i : Fin A.n} {y : E} (hy : y ∈ A.image i) (j : Fin (finrank ℝ F)) :
    (finBasis ℝ F).repr (A.coord i (toSection hp w) y) j =
      preciseRepresentative μ (W1p.value ((w : A.sectionChartData.SobolevData μ p 1) i j)) y := by
  rw [eqOn_coord_toSection_chartRep hp w i hy, chartRep, (finBasis ℝ F).repr_sum_self]

/-- **Morrey's embedding for Sobolev sections: the sup bound in charts.** For `p` above the
dimension, on every compact subset `K` of the image of chart `i` the chart expression of the
continuous representative of `w ∈ W^{1,p}(V)` is bounded by `C ‖w‖`, where `C` depends on `K` but
not on `w`. -/
theorem exists_forall_norm_coord_toSection_le (hp : (finrank ℝ E : ℝ≥0∞) < p) (i : Fin A.n)
    {K : Set E} (hK : IsCompact K) (hKi : K ⊆ A.image i) :
    ∃ C : ℝ, 0 < C ∧ ∀ (w : SobolevSection A μ p 1), ∀ y ∈ K,
      ‖A.coord i (toSection hp w) y‖ ≤ C * ‖w‖ := by
  obtain ⟨C, hC, hsup⟩ :=
    W1p.exists_forall_norm_preciseRepresentative_le_of_isCompact (mu := μ) hp hK hKi
  refine ⟨C * (1 + ∑ j, ‖finBasis ℝ F j‖), by positivity, fun w y hy ↦ ?_⟩
  rw [eqOn_coord_toSection_chartRep hp w i (hKi hy), chartRep]
  calc ‖∑ j, preciseRepresentative μ
          (W1p.value ((w : A.sectionChartData.SobolevData μ p 1) i j)) y • finBasis ℝ F j‖
      ≤ ∑ j, ‖preciseRepresentative μ
          (W1p.value ((w : A.sectionChartData.SobolevData μ p 1) i j)) y‖ *
            ‖finBasis ℝ F j‖ :=
        (norm_sum_le _ _).trans_eq (Finset.sum_congr rfl fun j _ ↦ norm_smul _ _)
    _ ≤ ∑ j, C * ‖w‖ * ‖finBasis ℝ F j‖ := by
        gcongr with j
        exact (hsup _ y hy).trans
          (mul_le_mul_of_nonneg_left (SectionChartData.norm_component_le w i j) hC.le)
    _ = C * (∑ j, ‖finBasis ℝ F j‖) * ‖w‖ := by
        rw [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ ↦ by ring
    _ ≤ C * (1 + ∑ j, ‖finBasis ℝ F j‖) * ‖w‖ := by
        gcongr
        linarith

/-- **Morrey's embedding for Sobolev sections: Hölder continuity in charts.** For `n < p ≤ ∞`,
where `n` is the dimension, on every compact subset `K` of the image of chart `i` the chart
expression of the continuous representative of `w ∈ W^{1,p}(V)` is Hölder continuous with exponent
`1 - n / p` and constant `C ‖w‖`, where `C` depends on `K` but not on `w`. -/
theorem exists_forall_holderOnWith_coord_toSection (hp : (finrank ℝ E : ℝ≥0∞) < p)
    (i : Fin A.n) {K : Set E} (hK : IsCompact K) (hKi : K ⊆ A.image i) :
    ∃ C : ℝ≥0, ∀ w : SobolevSection A μ p 1, HolderOnWith (C * ‖w‖₊)
      ((1 : ℝ≥0∞) - finrank ℝ E / p).toNNReal (A.coord i (toSection hp w)) K := by
  set α := ((1 : ℝ≥0∞) - finrank ℝ E / p).toNNReal
  obtain ⟨C, hC⟩ :=
    W1p.exists_forall_holderOnWith_preciseRepresentative_of_isCompact (mu := μ) hp hK hKi
  refine ⟨C * ∑ j, ‖finBasis ℝ F j‖₊, fun w ↦ HolderOnWith.of_dist_le fun x hx y hy ↦ ?_⟩
  set f : Fin (finrank ℝ F) → E → ℝ := fun j ↦ preciseRepresentative μ
    (W1p.value ((w : A.sectionChartData.SobolevData μ p 1) i j))
  rw [eqOn_coord_toSection_chartRep hp w i (hKi hx), eqOn_coord_toSection_chartRep hp w i (hKi hy),
    chartRep, chartRep, dist_eq_norm, ← Finset.sum_sub_distrib]
  calc ‖∑ j, (f j x • finBasis ℝ F j - f j y • finBasis ℝ F j)‖
      ≤ ∑ j, dist (f j x) (f j y) * ‖finBasis ℝ F j‖ := by
        refine (norm_sum_le _ _).trans_eq (Finset.sum_congr rfl fun j _ ↦ ?_)
        rw [← sub_smul, norm_smul, Real.norm_eq_abs, Real.dist_eq]
    _ ≤ ∑ j, C * ‖w‖ * dist x y ^ (α : ℝ) * ‖finBasis ℝ F j‖ := by
        gcongr with j
        refine ((hC _).dist_le hx hy).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
        have h : ((C * ‖(w : A.sectionChartData.SobolevData μ p 1) i j‖₊ : ℝ≥0) : ℝ) ≤
            C * ‖w‖ := by
          rw [NNReal.coe_mul, coe_nnNorm]
          exact mul_le_mul_of_nonneg_left (SectionChartData.norm_component_le w i j) C.coe_nonneg
        exact h
    _ = ↑((C * ∑ j, ‖finBasis ℝ F j‖₊) * ‖w‖₊) * dist x y ^ (α : ℝ) := by
        simp only [NNReal.coe_mul, NNReal.coe_sum, coe_nnNorm, Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ ↦ by ring

/-- **`W^{1,∞}` sections are Lipschitz in charts.** At the endpoint `p = ∞` the Morrey exponent
`1 - n / p` is `1`: on every compact subset `K` of the image of chart `i` the chart expression of
the continuous representative of `w ∈ W^{1,∞}(V)` is Lipschitz with constant `C ‖w‖`, where `C`
depends on `K` but not on `w`. -/
theorem exists_forall_lipschitzOnWith_coord_toSection (i : Fin A.n) {K : Set E}
    (hK : IsCompact K) (hKi : K ⊆ A.image i) :
    ∃ C : ℝ≥0, ∀ w : SobolevSection A μ ∞ 1,
      LipschitzOnWith (C * ‖w‖₊) (A.coord i (toSection (ENNReal.natCast_lt_top _) w)) K := by
  obtain ⟨C, hC⟩ :=
    exists_forall_holderOnWith_coord_toSection (μ := μ) (ENNReal.natCast_lt_top _) i hK hKi
  refine ⟨C, fun w ↦ holderOnWith_one.1 ?_⟩
  simpa only [ENNReal.div_top, tsub_zero, ENNReal.toNNReal_one] using hC w

/-- The restriction to a compact subset `K` of the image of chart `i` of the chart expression of the
continuous representative, as an element of the Hölder space `C^{0,α}(K; F)`, `α = 1 - n / p`. -/
private def coordHolder (hp : (finrank ℝ E : ℝ≥0∞) < p) (i : Fin A.n) (K : Set E)
    [CompactSpace K] (hKi : K ⊆ A.image i) (w : SobolevSection A μ p 1) :
    HolderSpace ((1 : ℝ≥0∞) - finrank ℝ E / p).toNNReal K F :=
  HolderSpace.ofBoundedContinuousFunction
    (BoundedContinuousFunction.mkOfCompact ⟨K.domRestrict (A.coord i (toSection hp w)),
      ((A.continuousOn_coord (continuous_toSection hp w) i).mono hKi).domRestrict⟩)
    (let ⟨_, hC⟩ := exists_forall_holderOnWith_coord_toSection hp i
      (isCompact_iff_compactSpace.2 ‹_›) hKi
    ⟨_, (hC w).holderWith⟩)

private theorem coe_coordHolder (hp : (finrank ℝ E : ℝ≥0∞) < p) (i : Fin A.n) (K : Set E)
    [CompactSpace K] (hKi : K ⊆ A.image i) (w : SobolevSection A μ p 1) :
    ⇑(coordHolder hp i K hKi w) = K.domRestrict (A.coord i (toSection hp w)) := by
  ext y
  simp [coordHolder, HolderSpace.ofBoundedContinuousFunction_apply]

/-- **Morrey's embedding for Sobolev sections, as a bounded operator into a Hölder space.** For
`n < p ≤ ∞`, where `n` is the dimension, and a compact subset `K` of the image of chart `i`,
restricting to `K` the chart expression of the continuous representative is a continuous linear map
from `W^{1,p}(V)` to the Banach space `C^{0,α}(K; F)` of `α`-Hölder functions, `α = 1 - n / p`,
with its supremum-plus-Hölder norm (`TauCeti.HolderSpace`). -/
def morreyEmbedding (hp : (finrank ℝ E : ℝ≥0∞) < p) (i : Fin A.n) (K : Set E) [CompactSpace K]
    (hKi : K ⊆ A.image i) :
    SobolevSection A μ p 1 →L[ℝ] HolderSpace ((1 : ℝ≥0∞) - finrank ℝ E / p).toNNReal K F :=
  LinearMap.mkContinuousOfExistsBound
    { toFun := coordHolder hp i K hKi
      map_add' w v := HolderSpace.ext fun y ↦ by
        rw [HolderSpace.add_apply, coe_coordHolder, coe_coordHolder, coe_coordHolder]
        simp only [Set.domRestrict_apply]
        rw [toSection_add, A.coord_add i _ _ (hKi y.2)]
      map_smul' c w := HolderSpace.ext fun y ↦ by
        rw [RingHom.id_apply, HolderSpace.smul_apply, coe_coordHolder, coe_coordHolder]
        simp only [Set.domRestrict_apply]
        rw [toSection_smul, A.coord_smul i _ _ (hKi y.2)] }
    (by
      have hK : IsCompact K := isCompact_iff_compactSpace.2 ‹_›
      obtain ⟨C₁, hC₁, h₁⟩ := exists_forall_norm_coord_toSection_le (μ := μ) hp i hK hKi
      obtain ⟨C₂, h₂⟩ := exists_forall_holderOnWith_coord_toSection (μ := μ) hp i hK hKi
      refine ⟨C₁ + C₂, fun w ↦ ?_⟩
      have hsup (y : K) : ‖coordHolder hp i K hKi w y‖ ≤ C₁ * ‖w‖ := by
        rw [coe_coordHolder, Set.domRestrict_apply]
        exact h₁ w y y.2
      have hhol : HolderWith (C₂ * ‖w‖₊) ((1 : ℝ≥0∞) - finrank ℝ E / p).toNNReal
          (coordHolder hp i K hKi w) := by
        rw [coe_coordHolder]
        exact (h₂ w).holderWith
      refine (HolderSpace.norm_le_of_norm_le_of_holderWith (by positivity) hsup hhol).trans_eq ?_
      rw [NNReal.coe_mul, coe_nnNorm]
      ring)

@[simp]
theorem morreyEmbedding_apply_apply (hp : (finrank ℝ E : ℝ≥0∞) < p) (i : Fin A.n) (K : Set E)
    [CompactSpace K] (hKi : K ⊆ A.image i) (w : SobolevSection A μ p 1) (y : K) :
    morreyEmbedding hp i K hKi w y = A.coord i (toSection hp w) y := by
  simp [morreyEmbedding, coe_coordHolder]

/-- **Compactness of Morrey's embedding.** For `n < p ≤ ∞`, where `n` is the dimension, and every
exponent `β < 1 - n / p`, the embedding of `W^{1,p}(V)` into the Hölder space `C^{0,β}(K; F)` on a
compact subset `K` of the image of chart `i` is a compact operator: it is
`TauCeti.SobolevSection.morreyEmbedding` followed by the compact inclusion
`C^{0,α}(K; F) → C^{0,β}(K; F)` of `TauCeti.HolderSpace.isCompactOperator_inclusionL`. -/
theorem isCompactOperator_inclusionL_comp_morreyEmbedding (hp : (finrank ℝ E : ℝ≥0∞) < p)
    (i : Fin A.n) (K : Set E) [CompactSpace K] (hKi : K ⊆ A.image i) {β : ℝ≥0}
    (hβ : β < ((1 : ℝ≥0∞) - finrank ℝ E / p).toNNReal) :
    IsCompactOperator ((HolderSpace.inclusionL (X := K) (Y := F) hβ.le).comp
      (morreyEmbedding (μ := μ) hp i K hKi)) :=
  (HolderSpace.isCompactOperator_inclusionL hβ).comp_clm _

end SobolevSection

end TauCeti
